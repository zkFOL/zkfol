//! Zinc+ driven from the BEAM: statements queue to the prover thread,
//! each call returns an id, and the verdict arrives as a message
//! `{:zinc_plus, id, result}` addressed to the caller.

pub mod config;
pub mod runtime;
pub mod wire;

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

use rustler::types::atom::{error, ok};
use rustler::{Encoder, Env, LocalPid, NifStruct, OwnedEnv};
use zinc_protocol::ZincPlusPiop;
use zinc_uair::Uair;

use config::{
    setup_big_pp, setup_huge_pp, setup_pp, BigCfg, BigInt, Cfg, HugeCfg, HugeInt, D, F,
    NUM_COLUMN_OPENINGS, PERFORM_CHECKS, REP_FACTOR,
};
use runtime::{Op, Permuted, RuntimeUair, Selected, Spec, Tie, SPEC};
use wire::{encode_proof, verify_proof, write_export, Binding, Payload, Statement};

const BACKEND: &str = "zinc-plus-66776a3";

#[derive(rustler::NifMap)]
struct PcsParams {
    rep_factor: usize,
    column_openings: usize,
    degree: usize,
    backend: String,
}

#[derive(rustler::NifMap)]
struct Report {
    prove_ms: f64,
    verify_ms: f64,
    num_vars: usize,
    public_cols: usize,
    proof_bytes: usize,
    backend: String,
}

mod atoms {
    rustler::atoms! { up, down, add, mul, constant = "const", zinc_plus }
}

struct Job {
    pid: LocalPid,
    id: u64,
    spec: Spec,
    payload: Payload,
    num_vars: usize,
    export: Option<String>,
    bindings: Vec<Binding>,
}

static JOBS: OnceLock<Mutex<Sender<Job>>> = OnceLock::new();
static NEXT_ID: AtomicU64 = AtomicU64::new(1);

fn decode_program(program: Vec<(rustler::types::atom::Atom, i64)>) -> Result<Vec<Op>, String> {
    program
        .into_iter()
        .map(|(op, arg)| {
            if op == atoms::up() {
                Ok(Op::Up(arg as usize))
            } else if op == atoms::down() {
                Ok(Op::Down(arg as usize))
            } else if op == atoms::constant() {
                Ok(Op::Const(arg))
            } else if op == atoms::add() {
                Ok(Op::Add)
            } else if op == atoms::mul() {
                Ok(Op::Mul)
            } else {
                Err("unknown op".to_string())
            }
        })
        .collect()
}

/// One queued UAIR, as Elixir's Payload struct decodes.
#[derive(NifStruct)]
#[module = "Zkfol.ZincPlus.Payload"]
struct Request {
    num_cols: usize,
    num_public: usize,
    shifts: Vec<(usize, usize)>,
    program: Vec<(rustler::types::atom::Atom, i64)>,
    cells: Payload,
    word_lookups: Vec<(usize, usize, usize)>,
    selected_lookups: Vec<Selected>,
    permuted_lookups: Vec<Permuted>,
    point_ties: Vec<Tie>,
    reads: Vec<(usize, Vec<usize>, usize)>,
    num_vars: usize,
    export: Option<String>,
    bindings: Vec<Binding>,
}

/// Queue the statement and return the id its verdict will answer to.
#[rustler::nif]
fn prove_fol(env: Env, request: Request) -> Result<u64, String> {
    let program = decode_program(request.program)?;
    let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
    let job = Job {
        pid: env.pid(),
        id,
        spec: Spec {
            num_cols: request.num_cols,
            num_public: request.num_public,
            shifts: request.shifts,
            program,
            word_lookups: request.word_lookups,
            selected: request.selected_lookups,
            permuted: request.permuted_lookups,
            point_ties: request.point_ties,
            reads: request.reads,
        },
        payload: request.cells,
        num_vars: request.num_vars,
        export: request.export,
        bindings: request.bindings,
    };

    JOBS.get_or_init(|| {
        let (jobs, queue) = channel();
        std::thread::spawn(move || prover(queue));
        Mutex::new(jobs)
    })
    .lock()
    .unwrap_or_else(|poisoned| poisoned.into_inner())
    .send(job)
    .map_err(|_| "the prover thread is gone".to_string())?;

    Ok(id)
}

/// The prover thread: the spec's only writer, one verdict at a time,
/// each sent to its statement's caller. Nothing may kill the thread;
/// queued statements are still owed their verdicts.
fn prover(queue: Receiver<Job>) {
    for job in queue {
        // The caller is owed a verdict even if handling the job panics
        // past verdict's own guards, so the address is kept out here.
        let (pid, id) = (job.pid, job.id);

        if let Err(payload) = catch_unwind(AssertUnwindSafe(|| verdict(job))) {
            send_verdict(pid, id, &Err(panic_said(payload.as_ref())));
        }
    }
}

/// What a panic said, so a refusal names its reason rather than the bare
/// fact of a panic. A misconfigured lookup width is caught this way.
fn panic_said(payload: &(dyn std::any::Any + Send)) -> String {
    let said = payload
        .downcast_ref::<&str>()
        .map(|s| (*s).to_string())
        .or_else(|| payload.downcast_ref::<String>().cloned());
    match said {
        Some(said) => format!("the prover panicked: {said}"),
        None => "the prover panicked".to_string(),
    }
}

/// Prove one statement and send the verdict home. A panicking prove
/// becomes an error verdict, not a dead thread.
fn verdict(job: Job) {
    let (pid, id) = (job.pid, job.id);
    let num_public = job.spec.num_public;
    // The statement carries only the public columns: what a verifier is told.
    let export = job.export.map(|prefix| {
        let public = job.payload.public(num_public);
        (
            prefix,
            Statement { num_vars: job.num_vars, spec: job.spec.clone(), public, bindings: job.bindings },
        )
    });
    *SPEC.lock().unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(job.spec);

    let verdict = catch_unwind(AssertUnwindSafe(|| {
        run(job.payload, job.num_vars, num_public, export)
    }))
    .unwrap_or_else(|payload| Err(panic_said(payload.as_ref())));

    send_verdict(pid, id, &verdict);
}

/// Mail the verdict to its caller as `{:zinc_plus, id, {:ok | :error, _}}`.
fn send_verdict(pid: LocalPid, id: u64, verdict: &Result<Report, String>) {
    let mut env = OwnedEnv::new();
    let _ = env.send_and_clear(&pid, |env| {
        let outcome = match verdict {
            Ok(report) => (ok(), report).encode(env),
            Err(reason) => (error(), reason).encode(env),
        };
        (atoms::zinc_plus(), id, outcome).encode(env)
    });
}

/// The one prove-and-verify driver, expanded per configuration: a macro
/// rather than a generic, so the trait bounds live only in zinc-plus.
macro_rules! prove_verify {
    ($cfg:ty, $cell:ty, $pp:expr, $trace:expr, $num_vars:expr, $public:expr, $backend:expr, $export:expr) => {{
        let started = Instant::now();
        let proof = ZincPlusPiop::<$cfg, RuntimeUair<$cell>, F, D>::prove::<false, PERFORM_CHECKS>(
            &$pp,
            &$trace,
            $num_vars,
            zinc_protocol::project_scalar_fn,
        )
        .map_err(|e| format!("prover failed: {e:?}"))?;
        let prove_ms = started.elapsed().as_secs_f64() * 1000.0;
        let encoded = encode_proof(&proof);
        let proof_bytes = encoded.len();

        let sig = RuntimeUair::<$cell>::signature();
        let public_trace = $trace.public(&sig);

        let started = Instant::now();
        verify_proof!($cfg, $cell, $pp, proof, public_trace, $num_vars)?;
        let verify_ms = started.elapsed().as_secs_f64() * 1000.0;

        // Only a proof that verified is ever written, so a false statement leaves no file.
        if let Some((prefix, statement)) = &$export {
            write_export(prefix, statement, &encoded)?;
        }

        Ok(Report {
            prove_ms,
            verify_ms,
            num_vars: $num_vars,
            public_cols: $public,
            proof_bytes,
            backend: $backend,
        })
    }};
}

fn run(
    payload: Payload,
    num_vars: usize,
    public: usize,
    export: Option<(String, Statement)>,
) -> Result<Report, String> {
    match payload {
        Payload::I64(columns) => {
            let trace = runtime::trace(columns, num_vars);
            let pp = setup_pp(num_vars)?;
            prove_verify!(Cfg, i64, pp, trace, num_vars, public, BACKEND.to_string(), export)
        }
        Payload::Big(columns) => {
            let trace = runtime::limb_trace::<12>(columns, num_vars);
            let pp = setup_big_pp(num_vars)?;
            prove_verify!(
                BigCfg,
                BigInt,
                pp,
                trace,
                num_vars,
                public,
                format!("{BACKEND}/int768"),
                export
            )
        }
        Payload::Huge(columns) => {
            let trace = runtime::limb_trace::<110>(columns, num_vars);
            let pp = setup_huge_pp(num_vars)?;
            prove_verify!(
                HugeCfg,
                HugeInt,
                pp,
                trace,
                num_vars,
                public,
                format!("{BACKEND}/int7040"),
                export
            )
        }
    }
}

/// The commitment a proof of this statement would carry to its witness, without proving:
/// the integer tier only, and the witness columns are those after the public ones.
#[rustler::nif(schedule = "DirtyCpu")]
fn commit_fol(request: Request) -> Result<String, String> {
    match request.cells {
        Payload::I64(columns) => {
            wire::commit_witness(columns[request.num_public..].to_vec(), request.num_vars)
        }
        _ => Err("commit supports the i64 tier only".to_string()),
    }
}

/// The pinned code's parameters, asked of the backend rather than quoted:
/// they move with the dep, so a caller that reads them here cannot go
/// stale the way a copy would. A column of `2^num_vars` cells encodes to
/// `rep_factor` times that, and an opening reveals `column_openings` of
/// the codeword's positions.
#[rustler::nif]
fn pcs_params() -> PcsParams {
    PcsParams {
        rep_factor: REP_FACTOR,
        column_openings: NUM_COLUMN_OPENINGS,
        degree: D,
        backend: BACKEND.to_string(),
    }
}

rustler::init!("Elixir.Zkfol.ZincPlus.Native");

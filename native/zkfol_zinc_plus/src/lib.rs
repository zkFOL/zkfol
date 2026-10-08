//! Zinc+ driven from the BEAM: statements queue to the prover thread,
//! each call returns an id, and the verdict arrives as a message
//! `{:zinc_plus, id, result}` addressed to the caller.

mod config;
mod runtime;

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

use crypto_primitives::PrimeField;
use rustler::types::atom::{error, ok};
use rustler::{Encoder, Env, LocalPid, NifStruct, NifTaggedEnum, OwnedEnv};
use serde::{Deserialize, Serialize};
use zinc_protocol::{Proof, ZincPlusPiop};
use zinc_transcript::traits::GenTranscribable;
use zinc_transcript::traits::Transcribable;
use zinc_uair::{ideal::DegreeOneIdeal, ideal_collector::IdealOrZero, Uair};

use config::{
    setup_big_pp, setup_huge_pp, setup_pp, BigCfg, BigInt, Cfg, HugeCfg, HugeInt, D, F,
    NUM_COLUMN_OPENINGS, PERFORM_CHECKS, REP_FACTOR,
};
use runtime::{Op, Permuted, RuntimeUair, Selected, Spec, Tie, SPEC};

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

/// The trace payload as Elixir tags it, one variant per cell width.
#[derive(NifTaggedEnum, Serialize, Deserialize)]
enum Payload {
    I64(Vec<Vec<i64>>),
    Big(Vec<Vec<Vec<u64>>>),
    Huge(Vec<Vec<Vec<u64>>>),
}

/// What `zkfol_verify` checks a proof against: the spec, the cube size and the public columns.
#[derive(Serialize, Deserialize)]
struct Statement {
    num_vars: usize,
    spec: Spec,
    public: Payload,
}

struct Job {
    pid: LocalPid,
    id: u64,
    statement: Statement,
    payload: Payload,
    export: Option<String>,
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
}

/// Queue the statement and return the id its verdict will answer to.
#[rustler::nif]
fn prove_fol(env: Env, request: Request) -> Result<u64, String> {
    let program = decode_program(request.program)?;
    let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
    let job = Job {
        pid: env.pid(),
        id,
        statement: Statement {
            num_vars: request.num_vars,
            public: public(&request.cells, request.num_public),
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
        },
        payload: request.cells,
        export: request.export,
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
    *SPEC.lock().unwrap_or_else(|poisoned| poisoned.into_inner()) =
        Some(job.statement.spec.clone());

    let verdict = catch_unwind(AssertUnwindSafe(|| {
        run(job.payload, job.statement, job.export)
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

/// Bind the payload's cell width: its configuration and cell types, its trace and its public
/// parameters, for `body`. A macro rather than a generic, so the trait bounds live only in
/// zinc-plus.
macro_rules! at_width {
    ($payload:expr, $num_vars:expr, |$zt:ident, $cell:ident, $trace:ident, $pp:ident| $body:expr) => {
        match $payload {
            Payload::I64(columns) => {
                type $zt = Cfg;
                type $cell = i64;
                let $trace = runtime::trace(columns, $num_vars);
                let $pp = setup_pp($num_vars)?;
                $body
            }
            Payload::Big(columns) => {
                type $zt = BigCfg;
                type $cell = BigInt;
                let $trace = runtime::limb_trace::<12>(columns, $num_vars);
                let $pp = setup_big_pp($num_vars)?;
                $body
            }
            Payload::Huge(columns) => {
                type $zt = HugeCfg;
                type $cell = HugeInt;
                let $trace = runtime::limb_trace::<110>(columns, $num_vars);
                let $pp = setup_huge_pp($num_vars)?;
                $body
            }
        }
    };
}

/// Prove the statement, write it and the proof to `export`, and check the proof as
/// `zkfol_verify` would.
fn run(payload: Payload, statement: Statement, export: Option<String>) -> Result<Report, String> {
    let (num_vars, public_cols) = (statement.num_vars, statement.spec.num_public);
    let backend = match payload {
        Payload::I64(_) => BACKEND.to_string(),
        Payload::Big(_) => format!("{BACKEND}/int768"),
        Payload::Huge(_) => format!("{BACKEND}/int7040"),
    };

    let (proof, prove_ms) = at_width!(payload, num_vars, |Zt, Cell, trace, pp| {
        let started = Instant::now();
        let proof = ZincPlusPiop::<Zt, RuntimeUair<Cell>, F, D>::prove::<false, PERFORM_CHECKS>(
            &pp,
            &trace,
            num_vars,
            zinc_protocol::project_scalar_fn,
        )
        .map_err(|e| format!("prover failed: {e:?}"))?;
        (proof, started.elapsed().as_secs_f64() * 1000.0)
    });
    let proof_bytes = proof.get_num_bytes();

    if let Some(prefix) = export {
        let mut bytes = vec![0u8; proof_bytes];
        proof.write_transcription_bytes_exact(&mut bytes);
        std::fs::write(
            format!("{prefix}.json"),
            serde_json::to_vec(&statement).unwrap(),
        )
        .and_then(|()| std::fs::write(format!("{prefix}.proof"), bytes))
        .map_err(|e| format!("export failed: {e}"))?;
    }

    let started = Instant::now();
    statement.verify(proof)?;
    let verify_ms = started.elapsed().as_secs_f64() * 1000.0;

    Ok(Report {
        prove_ms,
        verify_ms,
        num_vars,
        public_cols,
        proof_bytes,
        backend,
    })
}

impl Statement {
    fn verify(self, proof: Proof<F>) -> Result<(), String> {
        let num_vars = self.num_vars;
        *SPEC.lock().unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(self.spec);

        at_width!(self.public, num_vars, |Zt, Cell, trace, pp| {
            let proj_ideal = |ideal: &IdealOrZero<<RuntimeUair<Cell> as Uair>::Ideal>,
                              field_cfg: &<F as PrimeField>::Config| {
                ideal.map(|i| DegreeOneIdeal::from_with_cfg(i, field_cfg))
            };
            ZincPlusPiop::<Zt, RuntimeUair<Cell>, F, D>::verify::<_, { config::CHECK_OVERFLOW }>(
                &pp,
                proof,
                &trace,
                num_vars,
                zinc_protocol::project_scalar_fn,
                proj_ideal,
            )
            .map_err(|e| format!("verifier failed: {e:?}"))
        })
    }
}

/// Check the proof file against the statement file. A malformed proof panics the decoder.
pub fn check(statement: &str, proof: &str) -> Result<(), String> {
    let read = |path: &str| std::fs::read(path).map_err(|e| format!("{path}: {e}"));
    let statement: Statement =
        serde_json::from_slice(&read(statement)?).map_err(|e| format!("{statement}: {e}"))?;
    statement.verify(Proof::read_transcription_bytes_exact(&read(proof)?))
}

/// The first `n` columns of the payload, the public ones.
fn public(payload: &Payload, n: usize) -> Payload {
    match payload {
        Payload::I64(columns) => Payload::I64(columns[..n].to_vec()),
        Payload::Big(columns) => Payload::Big(columns[..n].to_vec()),
        Payload::Huge(columns) => Payload::Huge(columns[..n].to_vec()),
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

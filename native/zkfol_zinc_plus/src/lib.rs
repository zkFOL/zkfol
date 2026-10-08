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
use zinc_protocol::ZincPlusPiop;
use zinc_transcript::traits::Transcribable;
use zinc_uair::{ideal::DegreeOneIdeal, ideal_collector::IdealOrZero, Uair};

use config::{
    setup_big_pp, setup_huge_pp, setup_pp, BigCfg, BigInt, Cfg, HugeCfg, HugeInt, D, F,
    PERFORM_CHECKS,
};
use runtime::{Op, RuntimeUair, Spec, SPEC};

const BACKEND: &str = "zinc-plus-7cf72c4";

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
#[derive(NifTaggedEnum)]
enum Payload {
    I64(Vec<Vec<i64>>),
    Big(Vec<Vec<Vec<u64>>>),
    Huge(Vec<Vec<Vec<u64>>>),
}

struct Job {
    pid: LocalPid,
    id: u64,
    spec: Spec,
    payload: Payload,
    bins: Vec<Vec<u32>>,
    num_vars: usize,
    tamper: bool,
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

// The pin holds BitPoly lookups to witness binary columns of width D.
fn check_lookups(lookups: &[(usize, usize, usize)], bin_cols: usize) -> Result<(), String> {
    for &(col, width, chunk) in lookups {
        if col >= bin_cols {
            return Err(format!("lookup column {col} has no binary column"));
        }
        if width != D {
            return Err(format!("lookup width {width} must equal D = {D} at this pin"));
        }
        if chunk == 0 || width % chunk != 0 {
            return Err(format!("chunk width {chunk} must divide width {width}"));
        }
    }
    Ok(())
}

/// Queue the statement and return the id its verdict will answer to.
#[allow(clippy::too_many_arguments)]
fn submit(
    env: Env,
    num_cols: usize,
    num_public: usize,
    shifts: Vec<(usize, usize)>,
    program: Vec<(rustler::types::atom::Atom, i64)>,
    payload: Payload,
    bins: Vec<Vec<u32>>,
    lookups: Vec<(usize, usize, usize)>,
    reads: Vec<(usize, Vec<usize>, usize)>,
    num_vars: usize,
    tamper: bool,
) -> Result<u64, String> {
    let program = decode_program(program)?;
    check_lookups(&lookups, bins.len())?;
    let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
    let job = Job {
        pid: env.pid(),
        id,
        spec: Spec {
            num_cols,
            num_public,
            bin_cols: bins.len(),
            shifts,
            program,
            lookups,
            reads,
        },
        payload,
        bins,
        num_vars,
        tamper,
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

        if catch_unwind(AssertUnwindSafe(|| verdict(job))).is_err() {
            send_verdict(pid, id, &Err("the prover panicked".to_string()));
        }
    }
}

/// Prove one statement and send the verdict home. A panicking prove
/// becomes an error verdict, not a dead thread.
fn verdict(job: Job) {
    let (pid, id) = (job.pid, job.id);
    let num_public = job.spec.num_public;
    *SPEC.lock().unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(job.spec);

    let verdict = catch_unwind(AssertUnwindSafe(|| {
        run(job.payload, job.bins, job.num_vars, num_public, job.tamper)
    }))
    .unwrap_or_else(|_| Err("the prover panicked".to_string()));

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
    ($cfg:ty, $cell:ty, $pp:expr, $trace:expr, $num_vars:expr, $public:expr, $tamper:expr, $backend:expr) => {{
        let started = Instant::now();
        let mut proof = ZincPlusPiop::<$cfg, RuntimeUair<$cell>, F, D>::prove::<false, PERFORM_CHECKS>(
            &$pp,
            &$trace,
            $num_vars,
            zinc_protocol::project_scalar_fn,
        )
        .map_err(|e| format!("prover failed: {e:?}"))?;
        let prove_ms = started.elapsed().as_secs_f64() * 1000.0;
        let proof_bytes = proof.get_num_bytes();

        // The rejection experiment: bend one looked-up chunk lift, the
        // committed bit pattern's representative, and demand refusal.
        if $tamper {
            let group = proof
                .lookup_proof
                .groups
                .first_mut()
                .ok_or_else(|| "no lookup group to tamper".to_string())?;
            let coeff = &mut group.chunk_lifts[0][0].coeffs[0];
            *coeff = coeff.clone() + coeff.clone();
        }

        let sig = RuntimeUair::<$cell>::signature();
        let public_trace = $trace.public(&sig);

        let proj_ideal = |ideal: &IdealOrZero<<RuntimeUair<$cell> as Uair>::Ideal>,
                          field_cfg: &<F as PrimeField>::Config| {
            ideal.map(|i| DegreeOneIdeal::from_with_cfg(i, field_cfg))
        };

        let started = Instant::now();
        ZincPlusPiop::<$cfg, RuntimeUair<$cell>, F, D>::verify::<_, { config::CHECK_OVERFLOW }>(
            &$pp,
            proof,
            &public_trace,
            $num_vars,
            zinc_protocol::project_scalar_fn,
            proj_ideal,
        )
        .map_err(|e| format!("verifier failed: {e:?}"))?;
        let verify_ms = started.elapsed().as_secs_f64() * 1000.0;

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
    bins: Vec<Vec<u32>>,
    num_vars: usize,
    public: usize,
    tamper: bool,
) -> Result<Report, String> {
    match payload {
        Payload::I64(columns) => {
            let trace = runtime::trace(columns, bins, num_vars);
            let pp = setup_pp(num_vars)?;
            prove_verify!(Cfg, i64, pp, trace, num_vars, public, tamper, BACKEND.to_string())
        }
        Payload::Big(columns) => {
            let trace = runtime::limb_trace::<12>(columns, bins, num_vars);
            let pp = setup_big_pp(num_vars)?;
            prove_verify!(
                BigCfg,
                BigInt,
                pp,
                trace,
                num_vars,
                public,
                tamper,
                format!("{BACKEND}/int768")
            )
        }
        Payload::Huge(columns) => {
            let trace = runtime::limb_trace::<110>(columns, bins, num_vars);
            let pp = setup_huge_pp(num_vars)?;
            prove_verify!(
                HugeCfg,
                HugeInt,
                pp,
                trace,
                num_vars,
                public,
                tamper,
                format!("{BACKEND}/int7040")
            )
        }
    }
}

/// One queued UAIR: everything `submit` needs, decoded as a single struct
/// rather than eight positional arguments.
#[derive(NifStruct)]
#[module = "Zkfol.ZincPlus.Payload"]
struct Request {
    num_cols: usize,
    num_public: usize,
    shifts: Vec<(usize, usize)>,
    program: Vec<(rustler::types::atom::Atom, i64)>,
    cells: Payload,
    bins: Vec<Vec<u32>>,
    lookups: Vec<(usize, usize, usize)>,
    reads: Vec<(usize, Vec<usize>, usize)>,
    num_vars: usize,
    tamper: bool,
}

#[rustler::nif]
fn prove_fol(env: Env, request: Request) -> Result<u64, String> {
    submit(
        env,
        request.num_cols,
        request.num_public,
        request.shifts,
        request.program,
        request.cells,
        request.bins,
        request.lookups,
        request.reads,
        request.num_vars,
        request.tamper,
    )
}

rustler::init!("Elixir.Zkfol.ZincPlus");

//! The portable form of a proof: what a verifier on another machine receives.
//!
//! A proof travels as two files. `<prefix>.proof` is the protocol's own byte encoding of
//! the proof. `<prefix>.public.json` is a `Statement`: the circuit's spec, the tier and
//! the public columns, and nothing the prover kept private. The verifier needs no third
//! input, since the public parameters follow deterministically from `num_vars`.

use std::time::Instant;

use rustler::{NifStruct, NifTaggedEnum};
use serde::{Deserialize, Serialize};
use zinc_protocol::Proof;
use zinc_transcript::traits::{ConstTranscribable, GenTranscribable, Transcribable};
use zip_plus::pcs::structs::{ZipPlus, ZipPlusCommitment};

use crate::config::{setup_big_pp, setup_huge_pp, setup_pp, BigCfg, BigInt, Cfg, HugeCfg, HugeInt, F};
use crate::runtime::{self, Spec, SPEC};

/// The trace payload as Elixir tags it, one variant per cell width.
#[derive(NifTaggedEnum, Clone, Debug, Serialize, Deserialize)]
pub enum Payload {
    I64(Vec<Vec<i64>>),
    Big(Vec<Vec<Vec<u64>>>),
    Huge(Vec<Vec<Vec<u64>>>),
}

impl Payload {
    /// The first `n` columns: the public ones, which lead the trace.
    pub fn public(&self, n: usize) -> Payload {
        match self {
            Payload::I64(columns) => Payload::I64(columns[..n].to_vec()),
            Payload::Big(columns) => Payload::Big(columns[..n].to_vec()),
            Payload::Huge(columns) => Payload::Huge(columns[..n].to_vec()),
        }
    }
}

/// A named value the statement binds: the public cells, as `(column, row)`, that hold it.
/// The name is only a label. The cells are what the proof binds, and the verifier reads the
/// value from them.
#[derive(NifStruct, Clone, Debug, Serialize, Deserialize)]
#[module = "Zkfol.ZincPlus.Binding"]
pub struct Binding {
    pub name: String,
    pub cells: Vec<(usize, usize)>,
}

/// Everything a verifier is told besides the proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Statement {
    pub num_vars: usize,
    pub spec: Spec,
    pub public: Payload,
    #[serde(default)]
    pub bindings: Vec<Binding>,
}

/// What a verifier learns from an accepted proof.
pub struct Verified {
    pub verify_ms: f64,
    /// The proof's commitment to the witness columns, as hex.
    pub commitment: String,
    /// Each binding's value, as hex: its cells, eight hex digits each.
    pub bindings: Vec<(String, String)>,
}

/// The proof in the protocol's own little-endian, length-prefixed encoding.
pub fn encode_proof(proof: &Proof<F>) -> Vec<u8> {
    let mut bytes = vec![0u8; proof.get_num_bytes()];
    proof.write_transcription_bytes_exact(&mut bytes);
    bytes
}

/// Decode a proof, refusing bytes that do not round-trip to themselves. The decoder
/// panics on malformed input, so callers run this where a panic is a rejection.
fn decode_proof(bytes: &[u8]) -> Result<Proof<F>, String> {
    let proof = Proof::<F>::read_transcription_bytes_exact(bytes);
    match proof.get_num_bytes() == bytes.len() {
        true => Ok(proof),
        false => Err("proof bytes do not decode to a proof of their own length".to_string()),
    }
}

/// Write the proof and its public statement under `prefix`.
pub fn write_export(prefix: &str, statement: &Statement, proof: &[u8]) -> Result<(), String> {
    let public = serde_json::to_vec(statement).map_err(|e| format!("public inputs: {e}"))?;
    std::fs::write(format!("{prefix}.proof"), proof).map_err(|e| format!("proof file: {e}"))?;
    std::fs::write(format!("{prefix}.public.json"), public)
        .map_err(|e| format!("public inputs file: {e}"))
}

/// The one verify call, expanded per configuration like `prove_verify!`.
macro_rules! verify_proof {
    ($cfg:ty, $cell:ty, $pp:expr, $proof:expr, $public_trace:expr, $num_vars:expr) => {{
        let proj_ideal = |ideal: &zinc_uair::ideal_collector::IdealOrZero<
            <$crate::runtime::RuntimeUair<$cell> as zinc_uair::Uair>::Ideal,
        >,
                          field_cfg: &<$crate::config::F as crypto_primitives::PrimeField>::Config| {
            ideal.map(|i| zinc_uair::ideal::DegreeOneIdeal::from_with_cfg(i, field_cfg))
        };

        zinc_protocol::ZincPlusPiop::<
            $cfg,
            $crate::runtime::RuntimeUair<$cell>,
            $crate::config::F,
            { $crate::config::D },
        >::verify::<_, { $crate::config::PERFORM_CHECKS }>(
            &$pp,
            $proof,
            &$public_trace,
            $num_vars,
            zinc_protocol::project_scalar_fn,
            proj_ideal,
        )
        .map_err(|e| format!("verifier failed: {e:?}"))
    }};
}
pub(crate) use verify_proof;

/// The hex of one binding's cells read from the public columns, or `None` if it names a
/// cell that is not there.
fn bound_value(public: &Payload, binding: &Binding) -> Option<String> {
    binding
        .cells
        .iter()
        .map(|&(column, row)| match public {
            Payload::I64(columns) => columns.get(column)?.get(row).map(|v| format!("{v:08x}")),
            Payload::Big(columns) | Payload::Huge(columns) => {
                columns.get(column)?.get(row)?.first().map(|v| format!("{v:08x}"))
            }
        })
        .collect()
}

/// Verify encoded proof bytes against a statement. Panics on malformed input, so a caller
/// must treat a panic as a rejection.
pub fn verify_statement(statement: Statement, proof: &[u8]) -> Result<Verified, String> {
    let Statement { num_vars, spec, public, bindings } = statement;
    let proof = decode_proof(proof)?;
    let mut commitment = vec![0u8; ZipPlusCommitment::NUM_BYTES];
    proof.commitments.2.write_transcription_bytes_exact(&mut commitment);
    let bindings = bindings
        .iter()
        .map(|b| {
            bound_value(&public, b)
                .map(|value| (b.name.clone(), value))
                .ok_or_else(|| format!("binding {} names a cell outside the public columns", b.name))
        })
        .collect::<Result<Vec<_>, _>>()?;
    *SPEC.lock().unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(spec);

    let started = Instant::now();
    match public {
        Payload::I64(columns) => {
            let trace = runtime::trace(columns, num_vars);
            let pp = setup_pp(num_vars)?;
            verify_proof!(Cfg, i64, pp, proof, trace, num_vars)
        }
        Payload::Big(columns) => {
            let trace = runtime::limb_trace::<12>(columns, num_vars);
            let pp = setup_big_pp(num_vars)?;
            verify_proof!(BigCfg, BigInt, pp, proof, trace, num_vars)
        }
        Payload::Huge(columns) => {
            let trace = runtime::limb_trace::<110>(columns, num_vars);
            let pp = setup_huge_pp(num_vars)?;
            verify_proof!(HugeCfg, HugeInt, pp, proof, trace, num_vars)
        }
    }?;
    Ok(Verified {
        verify_ms: started.elapsed().as_secs_f64() * 1000.0,
        commitment: hex(&commitment),
        bindings,
    })
}

/// The commitment the prover would make to these witness columns, as hex: the proof's own
/// commitment, computed without proving. `columns` are the witness columns only, since the
/// public ones lead the trace and are not committed.
pub fn commit_witness(columns: Vec<Vec<i64>>, num_vars: usize) -> Result<String, String> {
    let trace = runtime::trace(columns, num_vars);
    let pp = setup_pp(num_vars)?;
    let (_hint, commitment) =
        ZipPlus::commit(&pp.2, &trace.int).map_err(|e| format!("commit: {e:?}"))?;
    let mut bytes = vec![0u8; ZipPlusCommitment::NUM_BYTES];
    commitment.write_transcription_bytes_exact(&mut bytes);
    Ok(hex(&bytes))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

//! The standalone verifier: a proof file and a public inputs file in, a verdict out.
//!
//! It reads nothing else, so it cannot see the text a proof is about. An optional third
//! argument is a pins file: a JSON object of expected values, by binding name, that the
//! proof must carry (the name `commitment` pins the proof's commitment to the witness).
//!
//! Exit status 0 is acceptance, 1 is rejection (including any panic while decoding a
//! malformed proof), 2 is a usage or unreadable-file error. One JSON line goes to stdout
//! either way.

use std::collections::BTreeMap;
use std::panic::catch_unwind;
use std::process::ExitCode;

use serde_json::json;
use zkfol_zinc_plus::wire::{verify_statement, Statement, Verified};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (proof_path, public_path, pins_path) = match args.as_slice() {
        [proof, public] => (proof, public, None),
        [proof, public, pins] => (proof, public, Some(pins)),
        _ => {
            eprintln!("usage: zkfol_verify <proof file> <public inputs file> [pins file]");
            return ExitCode::from(2);
        }
    };

    let read = |path: &String| std::fs::read(path);
    let (Ok(proof), Ok(public), pins) =
        (read(proof_path), read(public_path), pins_path.map(read).transpose())
    else {
        println!(r#"{{"verdict":"error","reason":"unreadable input file"}}"#);
        return ExitCode::from(2);
    };
    let Ok(pins) = pins else {
        println!(r#"{{"verdict":"error","reason":"unreadable pins file"}}"#);
        return ExitCode::from(2);
    };

    // A decoder panic is a rejection, not a crash report.
    std::panic::set_hook(Box::new(|_| {}));
    let verdict = catch_unwind(|| {
        let statement: Statement =
            serde_json::from_slice(&public).map_err(|e| format!("public inputs: {e}"))?;
        let verified = verify_statement(statement, &proof)?;
        pinned(&verified, pins.as_deref())?;
        Ok(verified)
    })
    .unwrap_or_else(|_| Err("malformed proof or public inputs".to_string()));

    match verdict {
        Ok(verified) => {
            println!(
                "{}",
                json!({
                    "verdict": "accept",
                    "verify_ms": (verified.verify_ms * 1000.0).round() / 1000.0,
                    "commitment": verified.commitment,
                    "bindings": verified.bindings.into_iter().collect::<BTreeMap<_, _>>(),
                })
            );
            ExitCode::SUCCESS
        }
        Err(reason) => {
            println!("{}", json!({ "verdict": "reject", "reason": reason }));
            ExitCode::from(1)
        }
    }
}

/// Every pinned value must be carried by the proof exactly.
fn pinned(verified: &Verified, pins: Option<&[u8]>) -> Result<(), String> {
    let Some(pins) = pins else { return Ok(()) };
    let pins: BTreeMap<String, String> =
        serde_json::from_slice(pins).map_err(|e| format!("pins file: {e}"))?;

    for (name, expected) in pins {
        let actual = match name.as_str() {
            "commitment" => Some(&verified.commitment),
            _ => verified.bindings.iter().find(|(n, _)| *n == name).map(|(_, v)| v),
        };
        match actual {
            Some(actual) if *actual == expected => {}
            Some(_) => return Err(format!("pin {name} does not match the proof")),
            None => return Err(format!("pin {name} is not carried by the proof")),
        }
    }
    Ok(())
}

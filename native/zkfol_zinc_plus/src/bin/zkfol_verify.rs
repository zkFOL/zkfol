//! `zkfol_verify <statement> <proof>`: exit 0 accepts the proof; anything else rejects it.
//! Take the statement from someone you trust, not from the prover: it says what is proved.

fn main() -> Result<(), String> {
    match std::env::args().skip(1).collect::<Vec<_>>().as_slice() {
        [statement, proof] => zkfol_zinc_plus::check(statement, proof),
        _ => Err("usage: zkfol_verify <statement> <proof>".to_string()),
    }
}

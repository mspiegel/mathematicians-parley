//! Whole numbers of any length are computed with, and every fact checks.
//!
//! `elab::numerals` builds closed facts about numerals from set.mm's tables
//! of digits and its decimal lemmas: sums, products, orders, memberships.
//! Each is written here as a theorem stating what the arithmetic says it is,
//! and the verifier the gate runs reads them all against set.mm. A fact
//! built wrong, or spelt otherwise than the statement spells the number, is
//! a proof the verifier refuses.
//!
//! This reads set.mm, and fails if set.mm cannot be found: a test that
//! skipped would say green about a thing it had not looked at.

use std::path::Path;
use std::rc::Rc;

use parley::elab::numerals;
use parley::mm::spell::Proof;
use parley::mm::{read, where_set_mm, Builder, Layered};
use parley::tools::verify::verified;

/// A whole number in set.mm's notation: `; ; 1 2 3` for 123.
fn written(n: u64) -> String {
    if n < 10 {
        n.to_string()
    } else {
        format!("; {} {}", written(n / 10), n % 10)
    }
}

/// Pairs to compute with: every pair of small numbers, which reaches every
/// entry of the tables and every carry, and a few long ones.
fn pairs() -> Vec<(u64, u64)> {
    let mut out: Vec<(u64, u64)> = Vec::new();
    for m in 0..=24 {
        for n in 0..=24 {
            out.push((m, n));
        }
    }
    out.extend([
        (99, 1),
        (1, 99),
        (987, 654),
        (999, 999),
        (100, 7),
        (45, 123),
        (1000, 10),
    ]);
    out
}

#[test]
fn numerals_of_any_length_are_computed_with() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let setmm = where_set_mm(None, root)
        .expect("set.mm not found; say where it is with SET_MM, or leave a copy or a link at the root of the working tree");
    let sigs = Rc::new(read(&[setmm.as_path()]).unwrap());
    let b = Builder::new(Layered::new(Rc::clone(&sigs)));

    let mut facts: Vec<(String, Proof)> = Vec::new();
    for (m, n) in pairs() {
        let (sm, sn) = (written(m), written(n));
        facts.push((
            format!("( {sm} + {sn} ) = {}", written(m + n)),
            numerals::sum(&b, m, n),
        ));
        facts.push((
            format!("( {sm} x. {sn} ) = {}", written(m * n)),
            numerals::product(&b, m, n),
        ));
        if m < n {
            facts.push((format!("{sm} < {sn}"), numerals::below(&b, m, n)));
        }
    }
    for n in [0, 1, 7, 10, 18, 40, 123] {
        let s = written(n);
        facts.push((format!("{s} e. NN0"), numerals::nn0(&b, n)));
        facts.push((format!("{s} e. CC"), numerals::cc(&b, n)));
        facts.push((format!("{s} e. RR"), numerals::re(&b, n)));
        if n > 0 {
            facts.push((format!("{s} e. NN"), numerals::nn(&b, n)));
            facts.push((format!("{s} =/= 0"), numerals::ne0(&b, n)));
            facts.push((format!("0 < {s}"), numerals::pos(&b, n)));
        }
    }

    let mut text = String::from("$[ set.mm $]\n");
    for (at, (says, proof)) in facts.iter().enumerate() {
        text += &format!("numeral-fact-{at} $p |- {says} $= {} $.\n", proof.text());
    }
    let setmm_bytes = std::fs::read(&setmm).unwrap();
    let problems = verified(vec![
        ("set.mm".to_string(), setmm_bytes),
        ("everything.mm".to_string(), text.into_bytes()),
    ]);
    assert!(
        problems.is_empty(),
        "{} of {} numeral facts are refused:\n{}",
        problems.len(),
        facts.len(),
        problems
            .iter()
            .take(5)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

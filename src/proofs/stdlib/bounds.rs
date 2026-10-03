//! A sequence with a limit is bounded, for `proved.mm`.
//!
//! The page says it as a textbook does: if x(n) → L as n → ∞ then some B is
//! at least every term. set.mm's `climbdd` bounds the absolute values of a
//! convergent sequence over an upper integer set; ℕ is the upper integers
//! from 1 (`nnuz`), and each term is its own absolute value or less
//! (`leabs`). The sequence the page writes as a rule in n is set.mm's map
//! ( n e. NN |-> B ), and its value at m is B with m for n (`fvmptg`), which
//! the lemma asks of the caller as set.mm's own lemmas do, ( n = m -> B = C ).
//! The map's letter and the bound's are two, so a scope holding the limit,
//! whose map binds n, never meets a condition on n. It is stated as a
//! deduction, as `climnnre` is.

use super::parallels::{statement, Prover, Said};
use crate::mm::Builder;
use crate::proofs::Lemma;

pub const HEAD: &str = "$( Bounds: a sequence with a limit is bounded above. $)
$( The map binds n and the bound counts by m, each kept out of what the
   other names; the bound x is apart from all three classes and from the
   hypotheses. $)
$d m n x $.
$d m B $.  $d n C $.
$d x A $.  $d x B $.  $d x C $.
$d m ph $.  $d x ph $.
";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![bounded(b)]
}

/// `gclimbdd`: ( ph -> E. x e. RR A. m e. NN C <_ x ), from every C real, the
/// map ( n e. NN |-> B ) tending to A, and C being B at m.
fn bounded(b: &mut Builder) -> Lemma {
    let hyps = [
        ("gclimbdd.1", "|- ( ( ph /\\ m e. NN ) -> C e. RR )"),
        ("gclimbdd.2", "|- ( ph -> ( n e. NN |-> B ) ~~> A )"),
        ("gclimbdd.3", "|- ( n = m -> B = C )"),
    ];
    for (label, said) in hyps {
        b.hypothesis(label, said);
    }
    let p = Prover { b };
    let given = |(label, said): (&str, &str)| Said {
        says: p.term(&said[3..], "wff"),
        proof: p.b.step(label),
    };
    let [real, tends, at_m] = hyps.map(given);
    let f = "( n e. NN |-> B )";

    // The map's value at m is C, a real and so a complex number.
    let m_in = p.by("simpr", &[], &[("ph", "ph"), ("ps", "m e. NN")]);
    let rule = p.by("eqid", &[], &[("A", f)]);
    let value = p.by("fvmptg", &[&at_m, &rule], &[("R", "RR")]);
    let value = p.by("syl2anc", &[&m_in, &real, &value], &[]);
    let complex = p.by("eqeltrd", &[&value, &p.by("recnd", &[&real], &[])], &[]);
    let every = p.by("ralrimiva", &[&complex], &[]);

    // It converges, so climbdd bounds its absolute values.
    let converges = p.by(
        "syl",
        &[
            &tends,
            &p.by(
                "releldmi",
                &[&p.by("climrel", &[], &[])],
                &[("A", f), ("B", "A")],
            ),
        ],
        &[],
    );
    let one = p.always(&p.by("1z", &[], &[]), "ph");
    let rule = p.by(
        "climbdd",
        &[&p.by("nnuz", &[], &[])],
        &[("F", f), ("k", "m"), ("x", "x")],
    );
    let bounded = p.by("syl3anc", &[&one, &converges, &every, &rule], &[]);

    // A term is at most its absolute value, so at most the bound.
    let at = "( ( ph /\\ x e. RR ) /\\ m e. NN )";
    let value = p.by("adantlr", &[&value], &[("th", "x e. RR")]);
    let real = p.by("adantlr", &[&real], &[("th", "x e. RR")]);
    let same = p.by("fveq2d", &[&value], &[("F", "abs")]);
    let below = "( abs ` ( ( n e. NN |-> B ) ` m ) ) <_ x";
    let held = p.by("simpr", &[], &[("ph", at), ("ps", below)]);
    let lift = |s: &Said| p.lift(s, below);
    let absolute = p.by("eqbrtrrd", &[&lift(&same), &held], &[]);
    let at_most = p.apply("leabs", &[&lift(&real)], &[]);
    let x_real = lift(&p.by(
        "simplr",
        &[],
        &[("ph", "ph"), ("ps", "x e. RR"), ("ch", "m e. NN")],
    ));
    let size = p.by("abscld", &[&p.by("recnd", &[&lift(&real)], &[])], &[]);
    let each = p.by(
        "letrd",
        &[&lift(&real), &size, &x_real, &at_most, &absolute],
        &[],
    );
    let each = p.by("ex", &[&each], &[("ph", at)]);
    let all = p.by("ralimdva", &[&each], &[]);
    let some = p.by("reximdva", &[&all], &[]);
    let said = p.is(
        p.by("mpd", &[&bounded, &some], &[]),
        "( ph -> E. x e. RR A. m e. NN C <_ x )",
    );
    Lemma::new("gclimbdd", statement(&p, &said), said.proof).with_hyps(&hyps)
}

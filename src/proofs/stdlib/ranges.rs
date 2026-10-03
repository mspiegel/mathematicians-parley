//! Sums over a range split in two and of a constant, for `proved.mm`.
//!
//! The page splits Σ(k = a to c) after b and counts a constant term
//! b − a + 1 times. set.mm says both of finite sets: `fsumsplit` of a set
//! that is the union of two disjoint ones, which `fzsplit2` and `fzdisj` make
//! of a range, and `fsumconst` with the size of the set, which `hashfz` gives
//! for a range. Each lemma asks what the page states, one hypothesis to a
//! fact, and is a deduction as set.mm's sum lemmas are.

use super::parallels::{statement, Prover, Said};
use crate::mm::Builder;
use crate::proofs::Lemma;

pub const HEAD: &str =
    "$( Ranges: a sum over a range split in two, and a sum of a constant. $)
$( The sum binds k, apart from the ends of the range, the constant and the
   hypotheses; the summand names it. $)
$d k K $.  $d k M $.  $d k N $.  $d k B $.  $d k ph $.
";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![split(b), constant(b)]
}

/// The hypotheses as proofs, registered first.
fn hypotheses<'h>(
    b: &mut Builder,
    said: &[(&'h str, &'h str)],
) -> Vec<(&'h str, &'h str)> {
    for (label, statement) in said {
        b.hypothesis(label, statement);
    }
    said.to_vec()
}

fn given(p: &Prover, (label, said): (&str, &str)) -> Said {
    Said {
        says: p.term(&said[3..], "wff"),
        proof: p.b.step(label),
    }
}

/// ( ph -> N e. ( ZZ>= ` M ) ), from M and N integers and M <_ N.
fn at_least(p: &Prover, m: &Said, n: &Said, order: &Said) -> Said {
    let three = p.by("3jca", &[m, n, order], &[]);
    let rule = p.by(
        "eluz2",
        &[],
        &[
            ("M", &p.show(&m.says.children()[1].children()[0])),
            ("N", &p.show(&n.says.children()[1].children()[0])),
        ],
    );
    p.by("sylibr", &[&three, &rule], &[])
}

/// `gfsumsplit`: Σ(k = M to N) A = Σ(k = M to K) A + Σ(k = K + 1 to N) A.
fn split(b: &mut Builder) -> Lemma {
    let hyps = hypotheses(
        b,
        &[
            ("gfsumsplit.1", "|- ( ph -> M e. ZZ )"),
            ("gfsumsplit.2", "|- ( ph -> K e. ZZ )"),
            ("gfsumsplit.3", "|- ( ph -> N e. ZZ )"),
            ("gfsumsplit.4", "|- ( ph -> M <_ ( K + 1 ) )"),
            ("gfsumsplit.5", "|- ( ph -> K <_ N )"),
            (
                "gfsumsplit.6",
                "|- ( ( ph /\\ k e. ( M ... N ) ) -> A e. RR )",
            ),
        ],
    );
    let p = Prover { b };
    let [m, k, n, low, high, term] = [0, 1, 2, 3, 4, 5].map(|i| given(&p, hyps[i]));
    let next = p.by("peano2zd", &[&k], &[]);
    let first = at_least(&p, &m, &next, &low);
    let second = at_least(&p, &k, &n, &high);
    let union = p.apply("fzsplit2", &[&first, &second], &[]);
    let before = p.by("ltp1d", &[&p.by("zred", &[&k], &[])], &[]);
    let apart = p.apply("fzdisj", &[&before], &[("J", "M"), ("N", "N")]);
    let finite = p.by("fzfid", &[], &[("ph", "ph"), ("M", "M"), ("N", "N")]);
    let complex = p.by("recnd", &[&term], &[]);
    let said = p.is(
        p.by("fsumsplit", &[&apart, &union, &finite, &complex], &[]),
        "( ph -> sum_ k e. ( M ... N ) A = ( sum_ k e. ( M ... K ) A + sum_ k e. ( ( K + 1 ) ... N ) A ) )",
    );
    Lemma::new("gfsumsplit", statement(&p, &said), said.proof).with_hyps(&hyps)
}

/// `gfsumconst`: Σ(k = M to N) B = ((N − M) + 1)·B.
fn constant(b: &mut Builder) -> Lemma {
    let hyps = hypotheses(
        b,
        &[
            ("gfsumconst.1", "|- ( ph -> M e. ZZ )"),
            ("gfsumconst.2", "|- ( ph -> N e. ZZ )"),
            ("gfsumconst.3", "|- ( ph -> M <_ N )"),
            ("gfsumconst.4", "|- ( ph -> B e. RR )"),
        ],
    );
    let p = Prover { b };
    let [m, n, order, value] = [0, 1, 2, 3].map(|i| given(&p, hyps[i]));
    let finite = p.by("fzfid", &[], &[("ph", "ph"), ("M", "M"), ("N", "N")]);
    let complex = p.by("recnd", &[&value], &[]);
    let sum = p.apply("fsumconst", &[&finite, &complex], &[("k", "k")]);
    let count = p.apply("hashfz", &[&at_least(&p, &m, &n, &order)], &[]);
    let count = p.by("oveq1d", &[&count], &[("C", "B"), ("F", "x.")]);
    let said = p.is(
        p.by("eqtrd", &[&sum, &count], &[]),
        "( ph -> sum_ k e. ( M ... N ) B = ( ( ( N - M ) + 1 ) x. B ) )",
    );
    Lemma::new("gfsumconst", statement(&p, &said), said.proof).with_hyps(&hyps)
}

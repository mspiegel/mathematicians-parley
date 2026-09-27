//! The value of a series, for `proved.mm`.
//!
//! The readable layer says a series is the limit of its partial sums: the
//! partial sums Σ(k = 1 to n) t(k) tend to L, so Σ(k = 1 to ∞) t(k) = L.
//! set.mm defines an infinite sum through a sequence of its own (`seq`), and
//! no single label says the readable form. `sersumlim` is it, from three
//! that together do: a sequence that tends to something converges
//! (`releldmi`, `climrel`); the partial sums of a convergent series tend to
//! its sum (`isumclim3`); and a sequence has one limit (`climuni`).
//!
//! It is stated as a deduction, as set.mm states its series lemmas:
//! `isumclim3` forbids the index in what the statement assumes, and the
//! partial sums bind it.
//!
//! The page defines a limit the way a textbook does: however small a
//! positive ε, there is a natural number N such that every term after the
//! N-th is within ε of the limit. set.mm's `clim2` says it over ℝ⁺, over an
//! upper integer set, and with each term complex, and it names its index
//! apart from the map's, so it cannot read a sequence written as a map.
//! `climnnre` is the page's form. `rlimclim` and `rlim2` give the limit of a
//! map over ℕ in the real sense, `ralrp` moves ε from ℝ⁺ to ℝ, and
//! `rexuzre` moves N from ℝ to ℕ.

use crate::binds;
use crate::mm::{Builder, Proof};
use crate::proofs::Lemma;

pub const HEAD: &str =
    "$( Series: the limit of a sequence as the page defines it, and the value
   of a series as the limit of its partial sums. $)
$d j k n $.
$d A j n x $.
$d B j x $.
$d ph j k n x $.

";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![limit(b), series(b)]
}

/// `climnnre`: a real sequence on ℕ tends to a real A exactly when, for
/// every positive x, some j ∈ ℕ has every later term within x of A.
fn limit(b: &mut Builder) -> Lemma {
    let f = "( n e. NN |-> B )";
    let near = "( abs ` ( B - A ) ) < x";
    let tail = format!("A. n e. NN ( j <_ n -> {near} )");
    let upper = format!("A. n e. ( ZZ>= ` j ) {near}");
    let real = ("climnnre.1", "|- ( ( ph /\\ n e. NN ) -> B e. RR )");
    let limit_real = ("climnnre.2", "|- ( ph -> A e. RR )");
    for (label, statement) in [real, limit_real] {
        b.hypothesis(label, statement);
    }
    let b: &Builder = b;
    let v = |var: &str| b.float(var);
    let ph = b.wff("ph");
    let at_n = b.wff("( ph /\\ n e. NN )");

    // The terms are complex, so the map is a sequence of complex numbers.
    let term = b.ap(
        "recnd",
        &binds! {"ph" => at_n.clone(), "A" => b.class("B")},
        &[&b.step(real.0)],
    );
    let to_cc = b.ap(
        "fmptd",
        &binds! {"ph" => ph.clone(), "x" => v("n"), "A" => b.class("NN"),
        "B" => b.class("B"), "C" => b.class("CC"),
        "F" => b.class(f)},
        &[&term, &b.ap("eqid", &binds! {"A" => b.class(f)}, &[])],
    );

    // On ℕ, which is an upper integer set, the two senses of limit agree,
    // and the real sense has an ε form for a map.
    let one_z = b.ap(
        "a1i",
        &binds! {"ph" => b.wff("1 e. ZZ"), "ps" => ph.clone()},
        &[&b.step("1z")],
    );
    let senses = b.ap(
        "rlimclim",
        &binds! {"ph" => ph.clone(), "A" => b.class("A"), "F" => b.class(f),
        "M" => b.class("1"), "Z" => b.class("NN")},
        &[&b.step("nnuz"), &one_z, &to_cc],
    );
    let q_rr = format!("E. j e. RR {tail}");
    let q_nn = format!("E. j e. NN {tail}");
    let eps = b.ap(
        "rlim2",
        &binds! {"ph" => ph.clone(), "x" => v("x"), "y" => v("j"), "z" => v("n"),
        "A" => b.class("NN"), "B" => b.class("B"),
        "C" => b.class("A")},
        &[
            &b.ap(
                "ralrimiva",
                &binds! {"ph" => ph.clone(), "ps" => b.wff("B e. CC"),
                "x" => v("n"), "A" => b.class("NN")},
                &[&term],
            ),
            &b.ap(
                "a1i",
                &binds! {"ph" => b.wff("NN C_ RR"), "ps" => ph.clone()},
                &[&b.step("nnssre")],
            ),
            &b.ap(
                "recnd",
                &binds! {"ph" => ph.clone(), "A" => b.class("A")},
                &[&b.step(limit_real.0)],
            ),
        ],
    );
    let plus = format!("A. x e. RR+ {q_rr}");
    let tends = format!("{f} ~~> A");
    let first = b.ap(
        "bitr3d",
        &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{f} ~~>r A")),
        "ch" => b.wff(&tends), "th" => b.wff(&plus)},
        &[&senses, &eps],
    );
    let over_rr = format!("A. x e. RR ( 0 < x -> {q_rr} )");
    let second = b.ap(
        "bitrdi",
        &binds! {"ph" => ph.clone(), "ps" => b.wff(&tends),
        "ch" => b.wff(&plus), "th" => b.wff(&over_rr)},
        &[
            &first,
            &b.ap("ralrp", &binds! {"ph" => b.wff(&q_rr), "x" => v("x")}, &[]),
        ],
    );

    // Past some real is past some natural number: for j ∈ ℕ, being in the
    // upper integers from j is, among the natural numbers, being at least j.
    let within = b.ap(
        "syl",
        &binds! {"ph" => b.wff("j e. NN"),
        "ps" => b.wff("( ZZ>= ` j ) C_ NN"),
        "ch" => b.wff(&format!("( {upper} <-> A. n e. NN ( n e. ( ZZ>= ` j ) -> {near} ) )"))},
        &[
            &b.ap("uznnssnn", &binds! {"N" => b.class("j")}, &[]),
            &b.ap(
                "ralss",
                &binds! {"ph" => b.wff(near), "x" => v("n"),
                "A" => b.class("( ZZ>= ` j )"),
                "B" => b.class("NN")},
                &[],
            ),
        ],
    );
    let both = b.wff("( j e. NN /\\ n e. NN )");
    let ints = b.ap(
        "anim12i",
        &binds! {"ph" => b.wff("j e. NN"), "ps" => b.wff("j e. ZZ"),
        "ch" => b.wff("n e. NN"), "th" => b.wff("n e. ZZ")},
        &[
            &b.ap("nnz", &binds! {"N" => b.class("j")}, &[]),
            &b.ap("nnz", &binds! {"N" => b.class("n")}, &[]),
        ],
    );
    let at_least = b.ap(
        "syl",
        &binds! {"ph" => both.clone(),
        "ps" => b.wff("( j e. ZZ /\\ n e. ZZ )"),
        "ch" => b.wff("( n e. ( ZZ>= ` j ) <-> j <_ n )")},
        &[
            &ints,
            &b.ap(
                "eluz",
                &binds! {"M" => b.class("j"), "N" => b.class("n")},
                &[],
            ),
        ],
    );
    let each = b.ap(
        "imbi1d",
        &binds! {"ph" => both.clone(),
        "ps" => b.wff("n e. ( ZZ>= ` j )"),
        "ch" => b.wff("j <_ n"), "th" => b.wff(near)},
        &[&at_least],
    );
    let among = b.ap(
        "ralbidva",
        &binds! {"ph" => b.wff("j e. NN"),
        "ps" => b.wff(&format!("( n e. ( ZZ>= ` j ) -> {near} )")),
        "ch" => b.wff(&format!("( j <_ n -> {near} )")),
        "x" => v("n"), "A" => b.class("NN")},
        &[&each],
    );
    let per_j = b.ap(
        "bitrd",
        &binds! {"ph" => b.wff("j e. NN"), "ps" => b.wff(&upper),
        "ch" => b.wff(&format!("A. n e. NN ( n e. ( ZZ>= ` j ) -> {near} )")),
        "th" => b.wff(&tail)},
        &[&within, &among],
    );
    let by_nn = b.ap(
        "rexbiia",
        &binds! {"ph" => b.wff(&upper), "ps" => b.wff(&tail),
        "x" => v("j"), "A" => b.class("NN")},
        &[&per_j],
    );
    let by_rr = b.ap(
        "ax-mp",
        &binds! {"ph" => b.wff("1 e. ZZ"),
        "ps" => b.wff(&format!("( E. j e. NN {upper} <-> {q_rr} )"))},
        &[
            &b.step("1z"),
            &b.ap(
                "rexuzre",
                &binds! {"ph" => b.wff(near), "j" => v("j"),
                "k" => v("n"), "M" => b.class("1"),
                "Z" => b.class("NN")},
                &[&b.step("nnuz")],
            ),
        ],
    );
    let moved = b.ap(
        "bitr3i",
        &binds! {"ph" => b.wff(&q_rr),
        "ps" => b.wff(&format!("E. j e. NN {upper}")),
        "ch" => b.wff(&q_nn)},
        &[&by_rr, &by_nn],
    );
    let over_nn = format!("A. x e. RR ( 0 < x -> {q_nn} )");
    let lifted = b.ap(
        "ralbii",
        &binds! {"ph" => b.wff(&format!("( 0 < x -> {q_rr} )")),
        "ps" => b.wff(&format!("( 0 < x -> {q_nn} )")),
        "x" => v("x"), "A" => b.class("RR")},
        &[&b.ap(
            "imbi2i",
            &binds! {"ph" => b.wff(&q_rr), "ps" => b.wff(&q_nn),
            "ch" => b.wff("0 < x")},
            &[&moved],
        )],
    );
    let proof = b.ap(
        "bitrdi",
        &binds! {"ph" => ph.clone(), "ps" => b.wff(&tends),
        "ch" => b.wff(&over_rr), "th" => b.wff(&over_nn)},
        &[&second, &lifted],
    );
    Lemma::new(
        "climnnre",
        format!("|- ( ph -> ( {tends} <-> {over_nn} ) )"),
        proof,
    )
    .with_hyps(&[real, limit_real])
}

/// `sersumlim`.
fn series(b: &mut Builder) -> Lemma {
    let g = "( n e. NN |-> sum_ k e. ( 1 ... n ) A )";
    let z = "( ZZ>= ` 1 )";
    let s = format!("sum_ k e. {z} A");
    let tends_said = format!("|- ( ph -> {g} ~~> B )");
    let real = ("sersumlim.1", "|- ( ( ph /\\ k e. NN ) -> A e. RR )");
    let tends = ("sersumlim.2", tends_said.as_str());
    for (label, statement) in [real, tends] {
        b.hypothesis(label, statement);
    }
    let b: &Builder = b;
    let v = |var: &str| b.float(var);
    let ph = b.wff("ph");

    // The partial sums converge, since they tend to B.
    let conv = b.step(tends.0);
    let dom = b.ap(
        "syl",
        &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{g} ~~> B")),
        "ch" => b.wff(&format!("{g} e. dom ~~>"))},
        &[
            &conv,
            &b.ap(
                "releldmi",
                &binds! {"A" => b.class(g), "B" => b.class("B"),
                "R" => b.class("~~>")},
                &[&b.step("climrel")],
            ),
        ],
    );

    // ( ( ph /\ name e. Z ) -> name e. NN ), since Z is ℕ.
    let natural = |name: &str| -> Proof {
        let under = format!("( ph /\\ {name} e. {z} )");
        b.ap(
            "eleqtrrdi",
            &binds! {"ph" => b.wff(&under), "A" => b.class(name),
            "B" => b.class(z), "C" => b.class("NN")},
            &[
                &b.ap(
                    "simpr",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{name} e. {z}"))},
                    &[],
                ),
                &b.step("nnuz"),
            ],
        )
    };

    // Each term is complex, from the first hypothesis.
    let at_k = format!("( ph /\\ k e. {z} )");
    let term = b.ap(
        "syl",
        &binds! {"ph" => b.wff(&at_k), "ps" => b.wff("A e. RR"),
        "ch" => b.wff("A e. CC")},
        &[
            &b.ap(
                "syl",
                &binds! {"ph" => b.wff(&at_k),
                "ps" => b.wff("( ph /\\ k e. NN )"),
                "ch" => b.wff("A e. RR")},
                &[
                    &b.ap(
                        "jca",
                        &binds! {"ph" => b.wff(&at_k), "ps" => ph.clone(),
                        "ch" => b.wff("k e. NN")},
                        &[
                            &b.ap(
                                "simpl",
                                &binds! {"ph" => ph.clone(),
                                "ps" => b.wff(&format!("k e. {z}"))},
                                &[],
                            ),
                            &natural("k"),
                        ],
                    ),
                    &b.step(real.0),
                ],
            ),
            &b.ap("recn", &binds! {"A" => b.class("A")}, &[]),
        ],
    );

    // The j-th partial sum is the sum to j, by the map's own rule.
    let at_j = format!("( ph /\\ j e. {z} )");
    let (upto_n, upto_j) = ("sum_ k e. ( 1 ... n ) A", "sum_ k e. ( 1 ... j ) A");
    let moved = b.ap(
        "syl",
        &binds! {"ph" => b.wff("n = j"),
        "ps" => b.wff("( 1 ... n ) = ( 1 ... j )"),
        "ch" => b.wff(&format!("{upto_n} = {upto_j}"))},
        &[
            &b.ap(
                "oveq2",
                &binds! {"A" => b.class("n"), "B" => b.class("j"),
                "C" => b.class("1"), "F" => b.class("...")},
                &[],
            ),
            &b.ap(
                "sumeq1",
                &binds! {"A" => b.class("( 1 ... n )"),
                "B" => b.class("( 1 ... j )"), "C" => b.class("A"),
                "k" => v("k")},
                &[],
            ),
        ],
    );
    let value = b.ap(
        "fvmptd3",
        &binds! {"ph" => b.wff(&at_j), "x" => v("n"), "A" => b.class("j"),
        "B" => b.class(upto_n), "C" => b.class(upto_j),
        "D" => b.class("NN"), "F" => b.class(g),
        "V" => b.class("_V")},
        &[
            &b.ap("eqid", &binds! {"A" => b.class(g)}, &[]),
            &moved,
            &natural("j"),
            &b.ap(
                "a1i",
                &binds! {"ph" => b.wff(&format!("{upto_j} e. _V")),
                "ps" => b.wff(&at_j)},
                &[&b.ap(
                    "sumex",
                    &binds! {"A" => b.class("( 1 ... j )"),
                    "B" => b.class("A"), "k" => v("k")},
                    &[],
                )],
            ),
        ],
    );

    // So the partial sums tend to the sum as well, and to B, and those are
    // one limit.
    let to_sum = b.ap(
        "isumclim3",
        &binds! {"ph" => ph.clone(), "A" => b.class("A"), "j" => v("j"),
        "k" => v("k"), "F" => b.class(g), "M" => b.class("1"),
        "Z" => b.class(z)},
        &[
            &b.ap("eqid", &binds! {"A" => b.class(z)}, &[]),
            &b.ap(
                "a1i",
                &binds! {"ph" => b.wff("1 e. ZZ"), "ps" => ph.clone()},
                &[&b.step("1z")],
            ),
            &dom,
            &term,
            &value,
        ],
    );
    let one = b.ap(
        "syl",
        &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("( {g} ~~> B /\\ {g} ~~> {s} )")),
        "ch" => b.wff(&format!("B = {s}"))},
        &[
            &b.ap(
                "jca",
                &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{g} ~~> B")),
                "ch" => b.wff(&format!("{g} ~~> {s}"))},
                &[&conv, &to_sum],
            ),
            &b.ap(
                "climuni",
                &binds! {"A" => b.class("B"), "B" => b.class(&s),
                "F" => b.class(g)},
                &[],
            ),
        ],
    );
    let proof = b.ap(
        "eqcomd",
        &binds! {"ph" => ph.clone(), "A" => b.class("B"), "B" => b.class(&s)},
        &[&one],
    );
    Lemma::new("sersumlim", format!("|- ( ph -> {s} = B )"), proof)
        .with_hyps(&[real, tends])
}

//! Groups, for `proved.mm`.
//!
//! What Lagrange's theorem asks of a group that set.mm says in several
//! steps: what is in a coset gH. set.mm's coset is the sum of the subsets
//! {g} and H (`LSSum`), and `lsmelvalx` says its members are the y·z with
//! y ∈ {g} and z ∈ H, which `rexsng` reads as the g·z with z ∈ H, for
//! `def:stdlib/groups/coset`.

use crate::binds;
use crate::mm::Builder;
use crate::proofs::Lemma;

pub const HEAD: &str = "$( Groups: what is in a coset. $)
$d y z A $.
$d y z S $.
$d y z X $.
$d y z G $.

";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![coset_member(b)]
}

/// ( ( G e. Grp /\ S C_ ( Base ` G ) /\ A e. ( Base ` G ) ) ->
/// ( X e. ( { A } ( LSSum ` G ) S ) <-> E. z e. S X = ( A ( +g ` G ) z ) ) )
fn coset_member(b: &Builder) -> Lemma {
    let (base, plus, sums) = ("( Base ` G )", "( +g ` G )", "( LSSum ` G )");
    let held = format!("( G e. Grp /\\ S C_ {base} /\\ A e. {base} )");
    let member = format!("X e. ( {{ A }} {sums} S )");
    let pairs = format!("E. y e. {{ A }} E. z e. S X = ( y {plus} z )");
    let ours = format!("E. z e. S X = ( A {plus} z )");
    let parts = binds! {"ph" => b.wff("G e. Grp"), "ps" => b.wff(&format!("S C_ {base}")),
    "ch" => b.wff(&format!("A e. {base}"))};
    let asked = format!("( G e. _V /\\ {{ A }} C_ {base} /\\ S C_ {base} )");
    // What lsmelvalx asks, from what the lemma is given.
    let set_g = b.ap(
        "syl",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff("G e. Grp"), "ch" => b.wff("G e. _V")},
        &[
            &b.ap("simp1", &parts, &[]),
            &b.ap("elex", &binds! {"A" => b.class("G"), "B" => b.class("Grp")}, &[]),
        ],
    );
    let single = b.ap(
        "syl",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff(&format!("A e. {base}")),
        "ch" => b.wff(&format!("{{ A }} C_ {base}"))},
        &[
            &b.ap("simp3", &parts, &[]),
            &b.ap(
                "snssi",
                &binds! {"A" => b.class("A"), "B" => b.class(base)},
                &[],
            ),
        ],
    );
    let asks = b.ap(
        "3jca",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff("G e. _V"),
        "ch" => b.wff(&format!("{{ A }} C_ {base}")),
        "th" => b.wff(&format!("S C_ {base}"))},
        &[&set_g, &single, &b.ap("simp2", &parts, &[])],
    );
    let summed = b.ap(
        "lsmelvalx",
        &binds! {"G" => b.class("G"), "V" => b.class("_V"),
        "T" => b.class("{ A }"), "U" => b.class("S"),
        "B" => b.class(base), "X" => b.class("X"),
        ".+" => b.class(plus), ".(+)" => b.class(sums),
        "y" => b.float("y"), "z" => b.float("z")},
        &[
            &b.ap("eqid", &binds! {"A" => b.class(base)}, &[]),
            &b.ap("eqid", &binds! {"A" => b.class(plus)}, &[]),
            &b.ap("eqid", &binds! {"A" => b.class(sums)}, &[]),
        ],
    );
    let first = b.ap(
        "syl",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff(&asked),
        "ch" => b.wff(&format!("( {member} <-> {pairs} )"))},
        &[&asks, &summed],
    );
    // The singleton's one member is A.
    let at_a = b.ap(
        "rexbidv",
        &binds! {"ph" => b.wff("y = A"),
        "ps" => b.wff(&format!("X = ( y {plus} z )")),
        "ch" => b.wff(&format!("X = ( A {plus} z )")),
        "x" => b.float("z"), "A" => b.class("S")},
        &[&b.ap(
            "eqeq2d",
            &binds! {"ph" => b.wff("y = A"),
            "A" => b.class(&format!("( y {plus} z )")),
            "B" => b.class(&format!("( A {plus} z )")),
            "C" => b.class("X")},
            &[&b.ap(
                "oveq1",
                &binds! {"A" => b.class("y"), "B" => b.class("A"),
                "C" => b.class("z"), "F" => b.class(plus)},
                &[],
            )],
        )],
    );
    let single_out = b.ap(
        "rexsng",
        &binds! {"x" => b.float("y"), "A" => b.class("A"),
        "V" => b.class(base),
        "ph" => b.wff(&format!("E. z e. S X = ( y {plus} z )")),
        "ps" => b.wff(&ours)},
        &[&at_a],
    );
    let second = b.ap(
        "syl",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff(&format!("A e. {base}")),
        "ch" => b.wff(&format!("( {pairs} <-> {ours} )"))},
        &[&b.ap("simp3", &parts, &[]), &single_out],
    );
    Lemma::new(
        "gelcoset",
        format!("|- ( {held} -> ( {member} <-> {ours} ) )"),
        b.ap(
            "bitrd",
            &binds! {"ph" => b.wff(&held), "ps" => b.wff(&member),
            "ch" => b.wff(&pairs), "th" => b.wff(&ours)},
            &[&first, &second],
        ),
    )
}

//! Functions and their images, for `proved.mm`.
//!
//! What Schröder–Bernstein asks of functions that set.mm says in two steps
//! and the page in one. Each lemma is a chain of two or three set.mm lemmas:
//!
//! - what is in an image: `fvelimab` says it of a function on A, which `ffn`
//!   reads off f : A → B, with its equation turned by `eqcom` to the page's
//!   u = f(s), for `def:stdlib/functions/image`;
//! - a value lies in the image of a set holding its point: `fnfvima`, with
//!   `ffn` the same way, for `mun:stdlib/functions/value-in-image`;
//! - a one-to-one function's inverse undoes it: `f1f1orn` makes it a
//!   bijection onto its range, where `f1ocnvfv1` applies, for
//!   `mun:stdlib/functions/inverse-value`;
//! - a function that is one-to-one and reaches every point is a bijection:
//!   `dffo3` reads the reaching as onto, `df-f1o` puts the two together, and
//!   `f1oeng` gives the bijection, for `mun:stdlib/functions/onto-bijection`;
//! - a map sends its domain into a set exactly when each value lies there:
//!   `fmpt` says it of a name for the map, and `eqid` names the map itself,
//!   for `mun:stdlib/functions/function-into`.

use crate::binds;
use crate::mm::Builder;
use crate::proofs::Lemma;

pub const HEAD: &str =
    "$( Functions: images, inverses, and a bijection from one-to-one and
   onto. $)
$d x y A $.
$d x y B $.
$d x y F $.
$d x D $.
$d x S $.

";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![
        image_member(b),
        inverse_value(b),
        onto_bijection(b),
        map_into(b),
        value_in_image(b),
    ]
}

/// ( ( F : A --> B /\ S C_ A ) -> ( D e. ( F " S ) <-> E. x e. S D = ( F ` x ) ) )
fn image_member(b: &Builder) -> Lemma {
    let held = "( F : A --> B /\\ S C_ A )";
    let member = "D e. ( F \" S )";
    let theirs = "E. x e. S ( F ` x ) = D";
    let ours = "E. x e. S D = ( F ` x )";
    let set_mm = b.ap(
        "sylan",
        &binds! {"ph" => b.wff("F : A --> B"), "ps" => b.wff("F Fn A"),
        "ch" => b.wff("S C_ A"),
        "th" => b.wff(&format!("( {member} <-> {theirs} )"))},
        &[
            &b.ap(
                "ffn",
                &binds! {"F" => b.class("F"), "A" => b.class("A"), "B" => b.class("B")},
                &[],
            ),
            &b.ap(
                "fvelimab",
                &binds! {"F" => b.class("F"), "A" => b.class("A"),
                "B" => b.class("S"), "C" => b.class("D"),
                "x" => b.float("x")},
                &[],
            ),
        ],
    );
    let turned = b.ap(
        "rexbii",
        &binds! {"ph" => b.wff("( F ` x ) = D"),
        "ps" => b.wff("D = ( F ` x )"),
        "x" => b.float("x"), "A" => b.class("S")},
        &[&b.ap(
            "eqcom",
            &binds! {"A" => b.class("( F ` x )"), "B" => b.class("D")},
            &[],
        )],
    );
    Lemma::new(
        "gfvelima",
        format!("|- ( {held} -> ( {member} <-> {ours} ) )"),
        b.ap(
            "bitrdi",
            &binds! {"ph" => b.wff(held), "ps" => b.wff(member),
            "ch" => b.wff(theirs), "th" => b.wff(ours)},
            &[&set_mm, &turned],
        ),
    )
}

/// ( ( F : A --> B /\ S C_ A /\ D e. S ) -> ( F ` D ) e. ( F " S ) )
fn value_in_image(b: &Builder) -> Lemma {
    let says = "( F ` D ) e. ( F \" S )";
    Lemma::new(
        "gfnfvima",
        format!("|- ( ( F : A --> B /\\ S C_ A /\\ D e. S ) -> {says} )"),
        b.ap(
            "syl3an1",
            &binds! {"ph" => b.wff("F : A --> B"),
            "ps" => b.wff("F Fn A"), "ch" => b.wff("S C_ A"),
            "th" => b.wff("D e. S"), "ta" => b.wff(says)},
            &[
                &b.ap(
                    "ffn",
                    &binds! {"F" => b.class("F"), "A" => b.class("A"), "B" => b.class("B")},
                    &[],
                ),
                &b.ap(
                    "fnfvima",
                    &binds! {"F" => b.class("F"), "A" => b.class("A"),
                    "S" => b.class("S"), "X" => b.class("D")},
                    &[],
                ),
            ],
        ),
    )
}

/// ( A. x e. A C e. B <-> ( x e. A |-> C ) : A --> B )
fn map_into(b: &Builder) -> Lemma {
    let mapped = "( x e. A |-> C )";
    Lemma::new(
        "gfmpt",
        format!("|- ( A. x e. A C e. B <-> {mapped} : A --> B )"),
        b.ap(
            "fmpt",
            &binds! {"x" => b.float("x"), "A" => b.class("A"),
            "C" => b.class("C"), "B" => b.class("B"),
            "F" => b.class(mapped)},
            &[&b.ap("eqid", &binds! {"A" => b.class(mapped)}, &[])],
        ),
    )
}

/// ( ( F : A -1-1-> B /\ C e. A ) -> ( `' F ` ( F ` C ) ) = C )
fn inverse_value(b: &Builder) -> Lemma {
    let back = "( `' F ` ( F ` C ) ) = C";
    Lemma::new(
        "gf1cnvfv1",
        format!("|- ( ( F : A -1-1-> B /\\ C e. A ) -> {back} )"),
        b.ap(
            "sylan",
            &binds! {"ph" => b.wff("F : A -1-1-> B"),
            "ps" => b.wff("F : A -1-1-onto-> ran F"),
            "ch" => b.wff("C e. A"), "th" => b.wff(back)},
            &[
                &b.ap(
                    "f1f1orn",
                    &binds! {"F" => b.class("F"), "A" => b.class("A"), "B" => b.class("B")},
                    &[],
                ),
                &b.ap(
                    "f1ocnvfv1",
                    &binds! {"F" => b.class("F"), "A" => b.class("A"),
                    "B" => b.class("ran F"), "C" => b.class("C")},
                    &[],
                ),
            ],
        ),
    )
}

/// ( ( A e. V /\ F : A -1-1-> B /\ A. y e. B E. x e. A y = ( F ` x ) ) -> A ~~ B )
fn onto_bijection(b: &Builder) -> Lemma {
    let reach = "A. y e. B E. x e. A y = ( F ` x )";
    let held = format!("( A e. V /\\ F : A -1-1-> B /\\ {reach} )");
    let parts = binds! {"ph" => b.wff("A e. V"), "ps" => b.wff("F : A -1-1-> B"),
    "ch" => b.wff(reach)};
    let injective = b.ap("simp2", &parts, &[]);
    let reaches = b.ap("simp3", &parts, &[]);
    let function = b.ap(
        "syl",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff("F : A -1-1-> B"),
        "ch" => b.wff("F : A --> B")},
        &[
            &injective,
            &b.ap(
                "f1f",
                &binds! {"F" => b.class("F"), "A" => b.class("A"), "B" => b.class("B")},
                &[],
            ),
        ],
    );
    let onto = b.ap(
        "mpbir2and",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff("F : A -onto-> B"),
        "ch" => b.wff("F : A --> B"), "th" => b.wff(reach)},
        &[
            &function,
            &reaches,
            &b.ap(
                "a1i",
                &binds! {"ph" => b.wff(&format!("( F : A -onto-> B <-> ( F : A --> B /\\ {reach} ) )")),
                "ps" => b.wff(&held)},
                &[&b.ap(
                    "dffo3",
                    &binds! {"F" => b.class("F"), "A" => b.class("A"),
                    "B" => b.class("B"), "x" => b.float("x"),
                    "y" => b.float("y")},
                    &[],
                )],
            ),
        ],
    );
    let both = b.ap(
        "mpbir2and",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff("F : A -1-1-onto-> B"),
        "ch" => b.wff("F : A -1-1-> B"),
        "th" => b.wff("F : A -onto-> B")},
        &[
            &injective,
            &onto,
            &b.ap(
                "a1i",
                &binds! {"ph" => b.wff("( F : A -1-1-onto-> B <-> ( F : A -1-1-> B /\\ F : A -onto-> B ) )"),
                "ps" => b.wff(&held)},
                &[&b.ap(
                    "df-f1o",
                    &binds! {"F" => b.class("F"), "A" => b.class("A"), "B" => b.class("B")},
                    &[],
                )],
            ),
        ],
    );
    Lemma::new(
        "gf1foen",
        format!("|- ( {held} -> A ~~ B )"),
        b.ap(
            "syl2anc",
            &binds! {"ph" => b.wff(&held), "ps" => b.wff("A e. V"),
            "ch" => b.wff("F : A -1-1-onto-> B"), "th" => b.wff("A ~~ B")},
            &[
                &b.ap("simp1", &parts, &[]),
                &both,
                &b.ap(
                    "f1oeng",
                    &binds! {"A" => b.class("A"), "C" => b.class("V"), "F" => b.class("F"),
                    "B" => b.class("B")},
                    &[],
                ),
            ],
        ),
    )
}

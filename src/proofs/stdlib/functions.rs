//! Functions and their images, for `proved.mm`.
//!
//! What Schröder–Bernstein asks of functions that set.mm says in two steps
//! and the page in one. Each lemma is a chain of two or three set.mm lemmas:
//!
//! - what is in an image: `fvelimab` says it of a function on A, which `ffn`
//!   reads off f : A → B, with its equation turned by `eqcom` to the page's
//!   u = f(s), for `mun:stdlib/functions/image`;
//! - a value lies in the image of a set holding its point: `fnfvima`, with
//!   `ffn` the same way, for `mun:stdlib/functions/value-in-image`;
//! - a one-to-one function's inverse undoes it: `f1f1orn` makes it a
//!   bijection onto its range, where `f1ocnvfv1` applies, for
//!   `mun:stdlib/functions/inverse-value`;
//! - a function that is one-to-one and reaches every point is a bijection:
//!   `dffo3` reads the reaching as onto, `df-f1o` puts the two together, and
//!   `f1oeng` gives the bijection, for `mun:stdlib/functions/bijection`;
//! - a bijection gives a function that reaches every point: `bren` gives
//!   one that is one-to-one and onto, `f1ofo` and `foelrn` say it reaches
//!   each point, and `encv` with `elmapg` puts it among the functions from
//!   A to B, which `df-rex` says is the "there is" over them, for
//!   `mun:stdlib/functions/bijection-onto`;
//! - a map sends its domain into a set exactly when each value lies there:
//!   `fmpt` says it of a name for the map, and `eqid` names the map itself,
//!   for `mun:stdlib/functions/function-into`.

use crate::binds;
use crate::mm::Builder;
use crate::proofs::Lemma;

pub const HEAD: &str =
    "$( Functions: images, inverses, a bijection from one-to-one and onto,
   and an onto function from a bijection. $)
$d f x y A $.
$d f x y B $.
$d x y F $.
$d x D $.
$d x S $.

";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![
        image_member(b),
        inverse_value(b),
        onto_bijection(b),
        bijection_onto(b),
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

/// ( A ~~ B -> E. f e. ( B ^m A ) A. y e. B E. x e. A y = ( f ` x ) )
fn bijection_onto(b: &Builder) -> Lemma {
    let paired = "A ~~ B";
    let bijective = "f : A -1-1-onto-> B";
    let held = format!("( {paired} /\\ {bijective} )");
    let maps = "( B ^m A )";
    let reaches = "E. x e. A y = ( f ` x )";
    let reach = format!("A. y e. B {reaches}");
    let found = format!("E. f e. {maps} {reach}");
    let fab = binds! {"F" => b.class("f"), "A" => b.class("A"), "B" => b.class("B")};
    let held_bijective = b.ap(
        "simpr",
        &binds! {"ph" => b.wff(paired), "ps" => b.wff(bijective)},
        &[],
    );
    // f reaches every point of B, since it is onto.
    let onto = b.ap(
        "syl",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff(bijective),
        "ch" => b.wff("f : A -onto-> B")},
        &[&held_bijective, &b.ap("f1ofo", &fab, &[])],
    );
    let each = b.ap(
        "sylan",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff("f : A -onto-> B"),
        "ch" => b.wff("y e. B"), "th" => b.wff(reaches)},
        &[
            &onto,
            &b.ap(
                "foelrn",
                &binds! {"F" => b.class("f"), "A" => b.class("A"), "B" => b.class("B"),
                "C" => b.class("y"), "x" => b.float("x")},
                &[],
            ),
        ],
    );
    let reached = b.ap(
        "ralrimiva",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff(reaches),
        "x" => b.float("y"), "A" => b.class("B")},
        &[&each],
    );
    // f is among the functions from A to B, both being sets.
    let function = b.ap(
        "syl",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff(bijective),
        "ch" => b.wff("f : A --> B")},
        &[&held_bijective, &b.ap("f1of", &fab, &[])],
    );
    let sets = b.ap(
        "syl",
        &binds! {"ph" => b.wff(paired), "ps" => b.wff("( A e. _V /\\ B e. _V )"),
        "ch" => b.wff("( B e. _V /\\ A e. _V )")},
        &[
            &b.ap(
                "encv",
                &binds! {"A" => b.class("A"), "B" => b.class("B")},
                &[],
            ),
            &b.ap(
                "pm3.22",
                &binds! {"ph" => b.wff("A e. _V"), "ps" => b.wff("B e. _V")},
                &[],
            ),
        ],
    );
    let member_is = format!("( f e. {maps} <-> f : A --> B )");
    let unpacked = b.ap(
        "syl",
        &binds! {"ph" => b.wff(paired), "ps" => b.wff("( B e. _V /\\ A e. _V )"),
        "ch" => b.wff(&member_is)},
        &[
            &sets,
            &b.ap(
                "elmapg",
                &binds! {"A" => b.class("B"), "B" => b.class("A"),
                "V" => b.class("_V"), "W" => b.class("_V"), "C" => b.class("f")},
                &[],
            ),
        ],
    );
    let member = b.ap(
        "mpbird",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff(&format!("f e. {maps}")),
        "ch" => b.wff("f : A --> B")},
        &[
            &function,
            &b.ap(
                "adantr",
                &binds! {"ph" => b.wff(paired), "ps" => b.wff(&member_is),
                "ch" => b.wff(bijective)},
                &[&unpacked],
            ),
        ],
    );
    let both = format!("( f e. {maps} /\\ {reach} )");
    let exhibited = b.ap(
        "jca",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff(&format!("f e. {maps}")),
        "ch" => b.wff(&reach)},
        &[&member, &reached],
    );
    // The bijection `bren` gives is carried under its own quantifier, so
    // that nothing discharges f from a formula that mentions it.
    let carried = b.ap(
        "eximdv",
        &binds! {"ph" => b.wff(paired), "ps" => b.wff(bijective),
        "ch" => b.wff(&both), "x" => b.float("f")},
        &[&b.ap(
            "ex",
            &binds! {"ph" => b.wff(paired), "ps" => b.wff(bijective),
            "ch" => b.wff(&both)},
            &[&exhibited],
        )],
    );
    let exists = b.ap(
        "mpd",
        &binds! {"ph" => b.wff(paired), "ps" => b.wff(&format!("E. f {bijective}")),
        "ch" => b.wff(&format!("E. f {both}"))},
        &[
            &b.ap(
                "biimpi",
                &binds! {"ph" => b.wff(paired), "ps" => b.wff(&format!("E. f {bijective}"))},
                &[&b.ap(
                    "bren",
                    &binds! {"A" => b.class("A"), "B" => b.class("B"), "f" => b.float("f")},
                    &[],
                )],
            ),
            &carried,
        ],
    );
    Lemma::new(
        "gbijonto",
        format!("|- ( {paired} -> {found} )"),
        b.ap(
            "sylibr",
            &binds! {"ph" => b.wff(paired), "ps" => b.wff(&format!("E. f {both}")),
            "ch" => b.wff(&found)},
            &[
                &exists,
                &b.ap(
                    "df-rex",
                    &binds! {"x" => b.float("f"), "A" => b.class(maps), "ph" => b.wff(&reach)},
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

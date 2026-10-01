//! Sets, for `proved.mm`.
//!
//! What the library says of sets that set.mm says in more than one step:
//!
//! - a part of a set is in its power set: `elpw2g` read one way by
//!   `biimpar`, closed so that a side condition's search may use it;
//! - what is in the parts of X with a property: `elrab` over the power set,
//!   and `elpw2g` reading a member of the power set as a part, for
//!   `mun:stdlib/sets/part-builder`;
//! - a finite set split into parts of one size m has (number of parts) · m
//!   elements, for `mun:stdlib/counting/partition-count`;
//! - a set of parts of a finite set is finite, for
//!   `mun:stdlib/counting/parts-finite`;
//! - a finite set and one in bijection with it have one size, for
//!   `mun:stdlib/counting/card-equal`.

use crate::binds;
use crate::mm::Builder;
use crate::proofs::Lemma;

pub const HEAD: &str =
    "$( Sets: the parts of a set with a property, and a set counted by the
   equal parts it splits into. $)
$d x ps $.
$d x A $.
$d x B $.
$d v w y z K $.
$d v w y z X $.
$d v w y z M $.
$d v w y z ph $.
$d x y z $.

";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![
        part_in_power(b),
        part_member(b),
        partition_count(b),
        parts_finite(b),
        card_equal(b),
    ]
}

/// ( ( A e. Fin /\ A ~~ B ) -> ( # ` A ) = ( # ` B ) )
///
/// B is finite as A is (`enfi`), and two finite sets in bijection have one
/// size (`hashen`).
fn card_equal(b: &Builder) -> Lemma {
    let ph = b.wff("( A e. Fin /\\ A ~~ B )");
    let finite = b.ap(
        "simpl",
        &binds! {"ph" => b.wff("A e. Fin"), "ps" => b.wff("A ~~ B")},
        &[],
    );
    let paired = b.ap(
        "simpr",
        &binds! {"ph" => b.wff("A e. Fin"), "ps" => b.wff("A ~~ B")},
        &[],
    );
    let other = b.ap(
        "mpbid",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("A e. Fin"), "ch" => b.wff("B e. Fin")},
        &[
            &finite,
            &b.ap(
                "syl",
                &binds! {"ph" => ph.clone(), "ps" => b.wff("A ~~ B"),
                "ch" => b.wff("( A e. Fin <-> B e. Fin )")},
                &[
                    &paired,
                    &b.ap("enfi", &binds! {"A" => b.class("A"), "B" => b.class("B")}, &[]),
                ],
            ),
        ],
    );
    let sizes = b.ap(
        "syl2anc",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("A e. Fin"), "ch" => b.wff("B e. Fin"),
        "th" => b.wff("( ( # ` A ) = ( # ` B ) <-> A ~~ B )")},
        &[
            &finite,
            &other,
            &b.ap("hashen", &binds! {"A" => b.class("A"), "B" => b.class("B")}, &[]),
        ],
    );
    let proof = b.ap(
        "mpbird",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("( # ` A ) = ( # ` B )"),
        "ch" => b.wff("A ~~ B")},
        &[&paired, &sizes],
    );
    Lemma::new(
        "gcardeq",
        "|- ( ( A e. Fin /\\ A ~~ B ) -> ( # ` A ) = ( # ` B ) )",
        proof,
    )
}

/// ( ph -> K e. Fin ), from X finite and every member of K a part of X.
///
/// K is a part of the power set of X, which is finite (`pwfi`), so K is
/// (`ssfi`).
fn parts_finite(b: &mut Builder) -> Lemma {
    let hyps = [
        ("gpartsfin.1", "|- ( ph -> X e. Fin )"),
        ("gpartsfin.2", "|- ( ph -> A. y e. K y C_ X )"),
    ];
    for (label, statement) in hyps {
        b.hypothesis(label, statement);
    }
    let b: &Builder = b;
    let ph = b.wff("ph");
    let finite = b.step(hyps[0].0);
    let within = b.step(hyps[1].0);
    let each = b.ap(
        "syl",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("A. y e. K y C_ X"),
        "ch" => b.wff("( y e. K -> y C_ X )")},
        &[
            &within,
            &b.ap(
                "rsp",
                &binds! {"ph" => b.wff("y C_ X"), "x" => b.float("y"), "A" => b.class("K")},
                &[],
            ),
        ],
    );
    let in_power = b.ap(
        "ssrdv",
        &binds! {"ph" => ph.clone(), "x" => b.float("y"), "A" => b.class("K"),
        "B" => b.class("~P X")},
        &[&b.ap(
            "syl6",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("y e. K"),
            "ch" => b.wff("y C_ X"),
            "th" => b.wff("y e. ~P X")},
            &[
                &each,
                &b.ap(
                    "biimpri",
                    &binds! {"ph" => b.wff("y e. ~P X"), "ps" => b.wff("y C_ X")},
                    &[&b.ap(
                        "velpw",
                        &binds! {"x" => b.float("y"), "A" => b.class("X")},
                        &[],
                    )],
                ),
            ],
        )],
    );
    let power_finite = b.ap(
        "sylib",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("X e. Fin"), "ch" => b.wff("~P X e. Fin")},
        &[&finite, &b.ap("pwfi", &binds! {"A" => b.class("X")}, &[])],
    );
    let proof = b.ap(
        "syl2anc",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("~P X e. Fin"), "ch" => b.wff("K C_ ~P X"),
        "th" => b.wff("K e. Fin")},
        &[
            &power_finite,
            &in_power,
            &b.ap("ssfi", &binds! {"A" => b.class("~P X"), "B" => b.class("K")}, &[]),
        ],
    );
    Lemma::new("gpartsfin", "|- ( ph -> K e. Fin )", proof).with_hyps(&hyps)
}

/// ( ph -> ( # ` X ) = ( ( # ` K ) x. M ) ), from X finite, the members of K
/// making up X, two of them that meet being equal, and each of size M in
/// NN0.
///
/// `hashiun` sums the sizes of a disjoint family of finite sets; the family
/// is finite since it is a part of the power set of X (`pwfi`, `ssfi`), each
/// member is finite as a part of X, and it is disjoint by `disjor` once "if
/// Y and Z meet they are equal" is read as "Y = Z or they do not meet".
/// `fsumconst` then counts a sum of M's.
///
/// Each hypothesis binds letters of its own, w for the union and v for the
/// sizes, so that a proof citing it answers each from a line spelt as that
/// line is; `cbviunv` and `cbvralvw` bring them to y here.
fn partition_count(b: &mut Builder) -> Lemma {
    let union = "U_ y e. K y";
    let meets = "A. x e. ( y i^i z ) y = z";
    let apart = "( y = z \\/ ( y i^i z ) = (/) )";
    let third = format!("|- ( ph -> A. y e. K A. z e. K {meets} )");
    let hyps = [
        ("gpartcnt.1", "|- ( ph -> X e. Fin )"),
        ("gpartcnt.2", "|- ( ph -> U_ w e. K w = X )"),
        ("gpartcnt.3", third.as_str()),
        ("gpartcnt.4", "|- ( ph -> A. v e. K ( # ` v ) = M )"),
        ("gpartcnt.5", "|- ( ph -> M e. NN0 )"),
    ];
    for (label, statement) in hyps {
        b.hypothesis(label, statement);
    }
    let b: &Builder = b;
    let ph = b.wff("ph");
    let finite = b.step(hyps[0].0);
    let whole_w = b.step(hyps[1].0);
    let pairs = b.step(hyps[2].0);
    let sizes_v = b.step(hyps[3].0);
    let m_nat = b.step(hyps[4].0);
    let whole = b.ap(
        "eqtr3id",
        &binds! {"ph" => ph.clone(), "A" => b.class(union),
        "B" => b.class("U_ w e. K w"), "C" => b.class("X")},
        &[
            &b.ap(
                "cbviunv",
                &binds! {"x" => b.float("w"), "y" => b.float("y"),
                "A" => b.class("K"), "B" => b.class("w"),
                "C" => b.class("y")},
                &[&b.ap("id", &binds! {"ph" => b.wff("w = y")}, &[])],
            ),
            &whole_w,
        ],
    );
    let sizes = b.ap(
        "sylib",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("A. v e. K ( # ` v ) = M"),
        "ch" => b.wff("A. y e. K ( # ` y ) = M")},
        &[
            &sizes_v,
            &b.ap(
                "cbvralvw",
                &binds! {"x" => b.float("v"), "y" => b.float("y"),
                "A" => b.class("K"), "ph" => b.wff("( # ` v ) = M"),
                "ps" => b.wff("( # ` y ) = M")},
                &[&b.ap(
                    "eqeq1d",
                    &binds! {"ph" => b.wff("v = y"), "A" => b.class("( # ` v )"),
                    "B" => b.class("( # ` y )"), "C" => b.class("M")},
                    &[&b.ap(
                        "fveq2",
                        &binds! {"A" => b.class("v"), "B" => b.class("y"),
                        "F" => b.class("#")},
                        &[],
                    )],
                )],
            ),
        ],
    );
    let at = b.wff("( ph /\\ y e. K )");

    // Each member is a part of X, so in its power set and finite.
    let within = b.ap(
        "sseqtrd",
        &binds! {"ph" => at.clone(), "A" => b.class("y"), "B" => b.class(union),
        "C" => b.class("X")},
        &[
            &b.ap(
                "adantl",
                &binds! {"ph" => b.wff("y e. K"), "ps" => b.wff(&format!("y C_ {union}")), "ch" => ph.clone()},
                &[&b.ap(
                    "ssiun2",
                    &binds! {"x" => b.float("y"), "A" => b.class("K"),
                    "B" => b.class("y")},
                    &[],
                )],
            ),
            &b.ap(
                "adantr",
                &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{union} = X")),
                "ch" => b.wff("y e. K")},
                &[&whole],
            ),
        ],
    );
    let member_finite = b.ap(
        "syl2anc",
        &binds! {"ph" => at.clone(), "ps" => b.wff("X e. Fin"), "ch" => b.wff("y C_ X"),
        "th" => b.wff("y e. Fin")},
        &[
            &b.ap(
                "adantr",
                &binds! {"ph" => ph.clone(), "ps" => b.wff("X e. Fin"),
                "ch" => b.wff("y e. K")},
                &[&finite],
            ),
            &within,
            &b.ap(
                "ssfi",
                &binds! {"A" => b.class("X"), "B" => b.class("y")},
                &[],
            ),
        ],
    );
    let in_power = b.ap(
        "ssrdv",
        &binds! {"ph" => ph.clone(), "x" => b.float("y"), "A" => b.class("K"),
        "B" => b.class("~P X")},
        &[&b.ap(
            "ex",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("y e. K"),
            "ch" => b.wff("y e. ~P X")},
            &[&b.ap(
                "sylibr",
                &binds! {"ph" => at.clone(), "ps" => b.wff("y C_ X"),
                "ch" => b.wff("y e. ~P X")},
                &[
                    &within,
                    &b.ap(
                        "velpw",
                        &binds! {"x" => b.float("y"), "A" => b.class("X")},
                        &[],
                    ),
                ],
            )],
        )],
    );
    let power_finite = b.ap(
        "sylib",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("X e. Fin"), "ch" => b.wff("~P X e. Fin")},
        &[&finite, &b.ap("pwfi", &binds! {"A" => b.class("X")}, &[])],
    );
    let family_finite = b.ap(
        "syl2anc",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("~P X e. Fin"), "ch" => b.wff("K C_ ~P X"),
        "th" => b.wff("K e. Fin")},
        &[
            &power_finite,
            &in_power,
            &b.ap("ssfi", &binds! {"A" => b.class("~P X"), "B" => b.class("K")}, &[]),
        ],
    );

    // Two members sharing a point are equal: so equal, or with nothing in
    // common, since sharing none is the other case (`r19.3rzv`).
    let meet = "( y i^i z )";
    let shared = format!("( {meet} =/= (/) -> y = z )");
    let either = b.ap(
        "3bitri",
        &binds! {"ph" => b.wff(&shared), "ps" => b.wff(&format!("( -. {meet} = (/) -> y = z )")),
        "ch" => b.wff(&format!("( {meet} = (/) \\/ y = z )")), "th" => b.wff(apart)},
        &[
            &b.ap(
                "imbi1i",
                &binds! {"ph" => b.wff(&format!("{meet} =/= (/)")),
                "ps" => b.wff(&format!("-. {meet} = (/)")),
                "ch" => b.wff("y = z")},
                &[&b.ap(
                    "df-ne",
                    &binds! {"A" => b.class(meet), "B" => b.class("(/)")},
                    &[],
                )],
            ),
            &b.ap(
                "pm4.64",
                &binds! {"ph" => b.wff(&format!("{meet} = (/)")),
                "ps" => b.wff("y = z")},
                &[],
            ),
            &b.ap(
                "orcom",
                &binds! {"ph" => b.wff(&format!("{meet} = (/)")),
                "ps" => b.wff("y = z")},
                &[],
            ),
        ],
    );
    let read = b.ap(
        "syl",
        &binds! {"ph" => b.wff(meets), "ps" => b.wff(&shared), "ch" => b.wff(apart)},
        &[
            &b.ap(
                "com12",
                &binds! {"ph" => b.wff(&format!("{meet} =/= (/)")),
                "ps" => b.wff(meets), "ch" => b.wff("y = z")},
                &[&b.ap(
                    "biimprd",
                    &binds! {"ph" => b.wff(&format!("{meet} =/= (/)")),
                    "ps" => b.wff("y = z"),
                    "ch" => b.wff(meets)},
                    &[&b.ap(
                        "r19.3rzv",
                        &binds! {"A" => b.class(meet),
                        "ph" => b.wff("y = z"),
                        "x" => b.float("x")},
                        &[],
                    )],
                )],
            ),
            &b.ap(
                "biimpi",
                &binds! {"ph" => b.wff(&shared), "ps" => b.wff(apart)},
                &[&either],
            ),
        ],
    );
    let every = b.ap(
        "ralimi",
        &binds! {"ph" => b.wff(&format!("A. z e. K {meets}")),
        "ps" => b.wff(&format!("A. z e. K {apart}")),
        "x" => b.float("y"), "A" => b.class("K")},
        &[&b.ap(
            "ralimi",
            &binds! {"ph" => b.wff(meets), "ps" => b.wff(apart),
            "x" => b.float("z"), "A" => b.class("K")},
            &[&read],
        )],
    );
    let disjoint = b.ap(
        "sylibr",
        &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("A. y e. K A. z e. K {apart}")),
        "ch" => b.wff("Disj_ y e. K y")},
        &[
            &b.ap(
                "syl",
                &binds! {"ph" => ph.clone(),
                "ps" => b.wff(&format!("A. y e. K A. z e. K {meets}")),
                "ch" => b.wff(&format!("A. y e. K A. z e. K {apart}"))},
                &[&pairs, &every],
            ),
            &b.ap(
                "disjor",
                &binds! {"i" => b.float("y"), "j" => b.float("z"),
                "A" => b.class("K"), "B" => b.class("y"), "C" => b.class("z")},
                &[&b.ap("id", &binds! {"ph" => b.wff("y = z")}, &[])],
            ),
        ],
    );

    // The count.
    let summed = b.ap(
        "hashiun",
        &binds! {"ph" => ph.clone(), "x" => b.float("y"), "A" => b.class("K"),
        "B" => b.class("y")},
        &[&family_finite, &member_finite, &disjoint],
    );
    let size = format!("( # ` {union} )");
    let same_set = b.ap(
        "fveq2d",
        &binds! {"ph" => ph.clone(), "A" => b.class(union), "B" => b.class("X"),
        "F" => b.class("#")},
        &[&whole],
    );
    let each = b.ap(
        "syl",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("A. y e. K ( # ` y ) = M"),
        "ch" => b.wff("sum_ y e. K ( # ` y ) = sum_ y e. K M")},
        &[
            &sizes,
            &b.ap(
                "sumeq2",
                &binds! {"k" => b.float("y"), "A" => b.class("K"),
                "B" => b.class("( # ` y )"),
                "C" => b.class("M")},
                &[],
            ),
        ],
    );
    let constant = b.ap(
        "syl2anc",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("K e. Fin"), "ch" => b.wff("M e. CC"),
        "th" => b.wff("sum_ y e. K M = ( ( # ` K ) x. M )")},
        &[
            &family_finite,
            &b.ap(
                "nn0cnd",
                &binds! {"ph" => ph.clone(), "A" => b.class("M")},
                &[&m_nat],
            ),
            &b.ap(
                "fsumconst",
                &binds! {"k" => b.float("y"), "A" => b.class("K"),
                "B" => b.class("M")},
                &[],
            ),
        ],
    );
    let to_sum = b.ap(
        "eqtr3d",
        &binds! {"ph" => ph.clone(), "A" => b.class(&size),
        "B" => b.class("( # ` X )"),
        "C" => b.class("sum_ y e. K ( # ` y )")},
        &[&same_set, &summed],
    );
    let to_ms = b.ap(
        "eqtrd",
        &binds! {"ph" => ph.clone(), "A" => b.class("( # ` X )"),
        "B" => b.class("sum_ y e. K ( # ` y )"),
        "C" => b.class("sum_ y e. K M")},
        &[&to_sum, &each],
    );
    let proof = b.ap(
        "eqtrd",
        &binds! {"ph" => ph.clone(), "A" => b.class("( # ` X )"),
        "B" => b.class("sum_ y e. K M"),
        "C" => b.class("( ( # ` K ) x. M )")},
        &[&to_ms, &constant],
    );
    Lemma::new(
        "gpartcnt",
        "|- ( ph -> ( # ` X ) = ( ( # ` K ) x. M ) )",
        proof,
    )
    .with_hyps(&hyps)
}

/// ( ( B e. V /\ A C_ B ) -> A e. ~P B )
fn part_in_power(b: &Builder) -> Lemma {
    Lemma::new(
        "gsspw",
        "|- ( ( B e. V /\\ A C_ B ) -> A e. ~P B )",
        b.ap(
            "biimpar",
            &binds! {"ph" => b.wff("B e. V"), "ps" => b.wff("A e. ~P B"),
            "ch" => b.wff("A C_ B")},
            &[&b.ap(
                "elpw2g",
                &binds! {"A" => b.class("A"), "B" => b.class("B"),
                "V" => b.class("V")},
                &[],
            )],
        ),
    )
}

/// ( B e. V -> ( A e. { x e. ~P B | ph } <-> ( A C_ B /\ ps ) ) ), from
/// ( x = A -> ( ph <-> ps ) )
fn part_member(b: &mut Builder) -> Lemma {
    let at = ("gelrabpw.1", "|- ( x = A -> ( ph <-> ps ) )");
    b.hypothesis(at.0, at.1);
    let b: &Builder = b;
    let built = "{ x e. ~P B | ph }";
    let member = format!("A e. {built}");
    let theirs = "( A e. ~P B /\\ ps )";
    let ours = "( A C_ B /\\ ps )";
    let elrab = b.ap(
        "elrab",
        &binds! {"x" => b.float("x"), "A" => b.class("A"),
        "B" => b.class("~P B"), "ph" => b.wff("ph"),
        "ps" => b.wff("ps")},
        &[&b.step(at.0)],
    );
    let part = b.ap(
        "anbi1d",
        &binds! {"ph" => b.wff("B e. V"), "ps" => b.wff("A e. ~P B"),
        "ch" => b.wff("A C_ B"), "th" => b.wff("ps")},
        &[&b.ap(
            "elpw2g",
            &binds! {"A" => b.class("A"), "B" => b.class("B"),
            "V" => b.class("V")},
            &[],
        )],
    );
    let proof = b.ap(
        "bitrid",
        &binds! {"ph" => b.wff(&member), "ps" => b.wff(theirs),
        "ch" => b.wff("B e. V"), "th" => b.wff(ours)},
        &[&elrab, &part],
    );
    Lemma::new(
        "gelrabpw",
        format!("|- ( B e. V -> ( {member} <-> {ours} ) )"),
        proof,
    )
    .with_hyps(&[at])
}

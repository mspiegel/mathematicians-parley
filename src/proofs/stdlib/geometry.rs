//! The geometry facts this corpus needs and set.mm lacks, for `proved.mm`.
//!
//! The corpus supplies an item in one of two ways: a set.mm label, or a
//! proof file in the readable layer. Some of the geometry items can take
//! neither. set.mm has no theorem stating them, and the readable layer
//! cannot state them either, because saying what they say means dividing
//! one point by another and naming the branch cut of the complex logarithm.
//! Those are the ℂ encoding, which `GEOMETRY.md` chose on the understanding
//! that it would reach the reader as dull facts and not as case splits
//! inside an argument.
//!
//! So they are proved here, below the readable layer, beside the other
//! library proofs and after `definitions.mm`'s `df-ang`. A proof file
//! includes what that writes; the database names these labels in a `target`
//! the way it names a set.mm label.

use indexmap::IndexMap;

use crate::binds;
use crate::mm::{Builder, Proof};
use crate::proofs::Lemma;

/// What `mun:stdlib/geometry/triangle` says of three points, as set.mm
/// writes it.
///
/// Three distinct points that are not collinear, and in the plane the three
/// being collinear is (r − p)/(q − p) being real.
fn triangle(p: &str, q: &str, r: &str) -> String {
    format!(
        "( ( ( -. {p} = {q} /\\ -. {q} = {r} ) /\\ -. {p} = {r} ) /\\ -. ( ( {r} - {p} ) / ( {q} - {p} ) ) e. RR )"
    )
}

/// ( under -> ( x - y ) =/= 0 ), given ( under -> -. x = y ).
///
/// A difference is zero exactly when the two are equal, so the point of the
/// step is to carry that across the negation.
fn differs(
    b: &Builder,
    under: &str,
    x: &str,
    y: &str,
    mem_x: &Proof,
    mem_y: &Proof,
    unequal: &Proof,
) -> Proof {
    let w = binds! {"ph" => b.wff(under), "A" => b.class(x), "B" => b.class(y)};
    b.ap(
        "mpbird",
        &binds! {"ph" => b.wff(under), "ps" => b.wff(&format!("( {x} - {y} ) =/= 0")),
        "ch" => b.wff(&format!("{x} =/= {y}"))},
        &[
            &b.ap("neqned", &w, &[unequal]),
            &b.ap(
                "necon3bid",
                &binds! {"ph" => b.wff(under), "A" => b.class(&format!("( {x} - {y} )")),
                "B" => b.class("0"), "C" => b.class(x), "D" => b.class(y)},
                &[&b.ap("subeq0ad", &w, &[mem_x, mem_y])],
            ),
        ],
    )
}

/// ( under -> -. y = x ), given ( under -> -. x = y ).
fn flipped(b: &Builder, under: &str, x: &str, y: &str, unequal: &Proof) -> Proof {
    b.ap(
        "neneqd",
        &binds! {"ph" => b.wff(under), "A" => b.class(y), "B" => b.class(x)},
        &[&b.ap(
            "necomd",
            &binds! {"ph" => b.wff(under), "A" => b.class(x), "B" => b.class(y)},
            &[&b.ap(
                "neqned",
                &binds! {"ph" => b.wff(under), "A" => b.class(x), "B" => b.class(y)},
                &[unequal],
            )],
        )],
    )
}

/// A proof of each of the three points' membership of ℂ, lifted past what
/// else the antecedent holds: `adantr` of `simp1`, `simp2`, `simp3`.
fn members(b: &Builder, points: &str, rest: &str) -> IndexMap<&'static str, Proof> {
    let member = |name: &str, which: &str| -> Proof {
        b.ap(
            "adantr",
            &binds! {"ph" => b.wff(points), "ps" => b.wff(&format!("{name} e. CC")),
            "ch" => b.wff(rest)},
            &[&b.ap(
                which,
                &binds! {"ph" => b.wff("A e. CC"), "ps" => b.wff("B e. CC"),
                "ch" => b.wff("C e. CC")},
                &[],
            )],
        )
    };
    let mut mem = IndexMap::new();
    mem.insert("A", member("A", "simp1"));
    mem.insert("B", member("B", "simp2"));
    mem.insert("C", member("C", "simp3"));
    mem
}

/// Reordering a triangle's vertices, and the fact underneath it.
///
/// A triangle is three distinct points that are not collinear, and in the
/// plane the three being collinear is (R − P)/(Q − P) being real. Swapping
/// two vertices inverts that quotient and rotating them replaces it by
/// (1 − t)/(−t); neither leaves the reals, so neither makes a triangle
/// collinear. `gtrirec` is the inversion and the rest is bookkeeping.
fn triangle_lemmas(b: &mut Builder) -> Vec<Lemma> {
    let mut out = Vec::new();

    // ( A / B ) is real and nonzero exactly when its inverse is, and its
    // inverse is ( B / A ). Everything below turns on this one step.
    let ph = "( ( A e. CC /\\ A =/= 0 ) /\\ ( B e. CC /\\ B =/= 0 ) )";
    let (quo, inv) = ("( A / B )", "( B / A )");
    let psi = format!("( {ph} /\\ {quo} e. RR )");
    let says = format!("|- ( {ph} -> ( {quo} e. RR -> {inv} e. RR ) )");
    {
        let b: &Builder = b;
        let is_real = b.ap(
            "simpr",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{quo} e. RR"))},
            &[],
        );
        let nonzero = b.ap(
            "adantr",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{quo} =/= 0")),
            "ch" => b.wff(&format!("{quo} e. RR"))},
            &[&b.ap(
                "divne0",
                &binds! {"A" => b.class("A"), "B" => b.class("B")},
                &[],
            )],
        );
        let recip = b.ap(
            "syl",
            &binds! {"ph" => b.wff(&psi),
            "ps" => b.wff(&format!("( {quo} e. RR /\\ {quo} =/= 0 )")),
            "ch" => b.wff(&format!("( 1 / {quo} ) e. RR"))},
            &[
                &b.ap(
                    "jca",
                    &binds! {"ph" => b.wff(&psi),
                    "ps" => b.wff(&format!("{quo} e. RR")),
                    "ch" => b.wff(&format!("{quo} =/= 0"))},
                    &[&is_real, &nonzero],
                ),
                &b.ap("rereccl", &binds! {"A" => b.class(quo)}, &[]),
            ],
        );
        let equals = b.ap(
            "adantr",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("( 1 / {quo} ) = {inv}")),
            "ch" => b.wff(&format!("{quo} e. RR"))},
            &[&b.ap(
                "recdiv",
                &binds! {"A" => b.class("A"), "B" => b.class("B")},
                &[],
            )],
        );
        let under = b.ap(
            "eqeltrrd",
            &binds! {"ph" => b.wff(&psi), "A" => b.class(&format!("( 1 / {quo} )")),
            "B" => b.class(inv), "C" => b.class("RR")},
            &[&equals, &recip],
        );
        out.push(Lemma::new(
            "gtrirec",
            says.clone(),
            b.ap(
                "ex",
                &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{quo} e. RR")),
                "ch" => b.wff(&format!("{inv} e. RR"))},
                &[&under],
            ),
        ));
    }
    b.define("gtrirec", &says);
    let b: &Builder = b;

    // Swapping the last two vertices. The three points are the same three,
    // so only the quotient moves, and it moves to its own inverse.
    let points = "( A e. CC /\\ B e. CC /\\ C e. CC )";
    let (given, want) = (triangle("A", "B", "C"), triangle("A", "C", "B"));
    let held = format!("( {points} /\\ {given} )");
    let mem = members(b, points, &given);
    let whole = b.ap(
        "simpr",
        &binds! {"ph" => b.wff(points), "ps" => b.wff(&given)},
        &[],
    );
    let apart_binds = binds! {"ph" => b.wff(&held),
    "ps" => b.wff("( ( -. A = B /\\ -. B = C ) /\\ -. A = C )"),
    "ch" => b.wff("-. ( ( C - A ) / ( B - A ) ) e. RR")};
    let apart = b.ap("simpld", &apart_binds, &[&whole]);
    let straight = b.ap("simprd", &apart_binds, &[&whole]);
    let pair_binds = binds! {"ph" => b.wff(&held),
    "ps" => b.wff("( -. A = B /\\ -. B = C )"),
    "ch" => b.wff("-. A = C")};
    let pair = b.ap("simpld", &pair_binds, &[&apart]);
    let not_ac = b.ap("simprd", &pair_binds, &[&apart]);
    let two = binds! {"ph" => b.wff(&held), "ps" => b.wff("-. A = B"),
    "ch" => b.wff("-. B = C")};
    let not_ab = b.ap("simpld", &two, &[&pair]);
    let not_bc = b.ap("simprd", &two, &[&pair]);

    // ( C - A ) and ( B - A ) are the two the quotient is built from, and
    // each is nonzero because A is neither of the other two vertices.
    let mut sides: IndexMap<String, (Proof, Proof)> = IndexMap::new();
    for (near, far, unequal) in [("B", "A", &not_ab), ("C", "A", &not_ac)] {
        sides.insert(
            format!("{near}{far}"),
            (
                b.ap(
                    "subcld",
                    &binds! {"ph" => b.wff(&held), "A" => b.class(near),
                    "B" => b.class(far)},
                    &[&mem[near], &mem[far]],
                ),
                differs(
                    b,
                    &held,
                    near,
                    far,
                    &mem[near],
                    &mem[far],
                    &flipped(b, &held, far, near, unequal),
                ),
            ),
        );
    }

    let (ba, ca) = ("( B - A )", "( C - A )");
    let antecedent = b.ap(
        "jca",
        &binds! {"ph" => b.wff(&held),
        "ps" => b.wff(&format!("( {ba} e. CC /\\ {ba} =/= 0 )")),
        "ch" => b.wff(&format!("( {ca} e. CC /\\ {ca} =/= 0 )"))},
        &[
            &b.ap(
                "jca",
                &binds! {"ph" => b.wff(&held), "ps" => b.wff(&format!("{ba} e. CC")),
                "ch" => b.wff(&format!("{ba} =/= 0"))},
                &[&sides["BA"].0, &sides["BA"].1],
            ),
            &b.ap(
                "jca",
                &binds! {"ph" => b.wff(&held), "ps" => b.wff(&format!("{ca} e. CC")),
                "ch" => b.wff(&format!("{ca} =/= 0"))},
                &[&sides["CA"].0, &sides["CA"].1],
            ),
        ],
    );
    let turned = b.ap(
        "mpd",
        &binds! {"ph" => b.wff(&held),
        "ps" => b.wff(&format!("-. ( {ca} / {ba} ) e. RR")),
        "ch" => b.wff(&format!("-. ( {ba} / {ca} ) e. RR"))},
        &[
            &straight,
            &b.ap(
                "con3d",
                &binds! {"ph" => b.wff(&held),
                "ps" => b.wff(&format!("( {ba} / {ca} ) e. RR")),
                "ch" => b.wff(&format!("( {ca} / {ba} ) e. RR"))},
                &[&b.ap(
                    "syl",
                    &binds! {"ph" => b.wff(&held),
                    "ps" => b.wff(&format!("( ( {ba} e. CC /\\ {ba} =/= 0 ) /\\ ( {ca} e. CC /\\ {ca} =/= 0 ) )")),
                    "ch" => b.wff(&format!("( ( {ba} / {ca} ) e. RR -> ( {ca} / {ba} ) e. RR )"))},
                    &[
                        &antecedent,
                        &b.ap(
                            "gtrirec",
                            &binds! {"A" => b.class(ba), "B" => b.class(ca)},
                            &[],
                        ),
                    ],
                )],
            ),
        ],
    );

    let built = b.ap(
        "jca",
        &binds! {"ph" => b.wff(&held),
        "ps" => b.wff("( ( -. A = C /\\ -. C = B ) /\\ -. A = B )"),
        "ch" => b.wff(&format!("-. ( {ba} / {ca} ) e. RR"))},
        &[
            &b.ap(
                "jca31",
                &binds! {"ph" => b.wff(&held), "ps" => b.wff("-. A = C"),
                "ch" => b.wff("-. C = B"), "th" => b.wff("-. A = B")},
                &[&not_ac, &flipped(b, &held, "B", "C", &not_bc), &not_ab],
            ),
            &turned,
        ],
    );
    out.push(Lemma::new(
        "gtriswap",
        format!("|- ( {points} -> ( {given} -> {want} ) )"),
        b.ap(
            "ex",
            &binds! {"ph" => b.wff(points), "ps" => b.wff(&given),
            "ch" => b.wff(&want)},
            &[&built],
        ),
    ));
    out
}

/// Rotating the vertices, which moves the quotient rather than inverting.
///
/// Swapping two vertices takes (C − A)/(B − A) to its own inverse, but
/// rotating them takes it to 1 − (C − B)/(A − B), so the step is an
/// identity of the field rather than one fact about reciprocals. The
/// identity holds because (A − B) − (C − B) is A − C, and dividing that by
/// A − B splits into the two quotients.
fn rotation(b: &mut Builder, out: &mut Vec<Lemma>) {
    let w3a = "( A e. CC /\\ B e. CC /\\ C e. CC )";
    let apart = "( ( A - B ) =/= 0 /\\ ( C - B ) =/= 0 )";
    let ph = format!("( {w3a} /\\ {apart} )");
    let (ab, cb, ac) = ("( A - B )", "( C - B )", "( A - C )");
    let (quo, inv) = (format!("( {ab} / {cb} )"), format!("( {cb} / {ab} )"));
    let goal = "( ( C - A ) / ( B - A ) )";
    let psi = format!("( {ph} /\\ {quo} e. RR )");
    let says = format!("|- ( {ph} -> ( {quo} e. RR -> {goal} e. RR ) )");
    {
        let b: &Builder = b;
        // One proof of ( ph -> claim ), lifted to ( psi -> claim ).
        let under = |claim: &str, proof: &Proof| -> Proof {
            b.ap(
                "adantr",
                &binds! {"ph" => b.wff(&ph), "ps" => b.wff(claim),
                "ch" => b.wff(&format!("{quo} e. RR"))},
                &[proof],
            )
        };
        let member = |name: &str, which: &str| -> Proof {
            under(
                &format!("{name} e. CC"),
                &b.ap(
                    "adantr",
                    &binds! {"ph" => b.wff(w3a), "ps" => b.wff(&format!("{name} e. CC")),
                    "ch" => b.wff(apart)},
                    &[&b.ap(
                        which,
                        &binds! {"ph" => b.wff("A e. CC"), "ps" => b.wff("B e. CC"),
                        "ch" => b.wff("C e. CC")},
                        &[],
                    )],
                ),
            )
        };
        let mut mem: IndexMap<&str, Proof> = IndexMap::new();
        mem.insert("A", member("A", "simp1"));
        mem.insert("B", member("B", "simp2"));
        mem.insert("C", member("C", "simp3"));
        let two = binds! {"ph" => b.wff(&format!("{ab} =/= 0")), "ps" => b.wff(&format!("{cb} =/= 0"))};
        let mut nz: IndexMap<&str, Proof> = IndexMap::new();
        for (side, pick) in [(ab, "simpl"), (cb, "simpr")] {
            nz.insert(
                side,
                under(
                    &format!("{side} =/= 0"),
                    &b.ap(
                        "adantl",
                        &binds! {"ph" => b.wff(apart), "ps" => b.wff(&format!("{side} =/= 0")),
                        "ch" => b.wff(w3a)},
                        &[&b.ap(pick, &two, &[])],
                    ),
                ),
            );
        }
        let mut cls: IndexMap<&str, Proof> = IndexMap::new();
        for (side, x, y) in [(ab, "A", "B"), (cb, "C", "B"), (ac, "A", "C")] {
            cls.insert(
                side,
                b.ap(
                    "subcld",
                    &binds! {"ph" => b.wff(&psi), "A" => b.class(x),
                    "B" => b.class(y)},
                    &[&mem[x], &mem[y]],
                ),
            );
        }

        // 1 - ( C - B ) / ( A - B ) is real, because the quotient the step
        // is given is, and a quotient is real exactly when its inverse is.
        let flipped_real = b.ap(
            "mpd",
            &binds! {"ph" => b.wff(&psi), "ps" => b.wff(&format!("{quo} e. RR")),
            "ch" => b.wff(&format!("{inv} e. RR"))},
            &[
                &b.ap(
                    "simpr",
                    &binds! {"ph" => b.wff(&ph), "ps" => b.wff(&format!("{quo} e. RR"))},
                    &[],
                ),
                &b.ap(
                    "syl",
                    &binds! {"ph" => b.wff(&psi),
                    "ps" => b.wff(&format!("( ( {ab} e. CC /\\ {ab} =/= 0 ) /\\ ( {cb} e. CC /\\ {cb} =/= 0 ) )")),
                    "ch" => b.wff(&format!("( {quo} e. RR -> {inv} e. RR )"))},
                    &[
                        &b.ap(
                            "jca",
                            &binds! {"ph" => b.wff(&psi),
                            "ps" => b.wff(&format!("( {ab} e. CC /\\ {ab} =/= 0 )")),
                            "ch" => b.wff(&format!("( {cb} e. CC /\\ {cb} =/= 0 )"))},
                            &[
                                &b.ap(
                                    "jca",
                                    &binds! {"ph" => b.wff(&psi), "ps" => b.wff(&format!("{ab} e. CC")),
                                    "ch" => b.wff(&format!("{ab} =/= 0"))},
                                    &[&cls[ab], &nz[ab]],
                                ),
                                &b.ap(
                                    "jca",
                                    &binds! {"ph" => b.wff(&psi), "ps" => b.wff(&format!("{cb} e. CC")),
                                    "ch" => b.wff(&format!("{cb} =/= 0"))},
                                    &[&cls[cb], &nz[cb]],
                                ),
                            ],
                        ),
                        &b.ap(
                            "gtrirec",
                            &binds! {"A" => b.class(ab), "B" => b.class(cb)},
                            &[],
                        ),
                    ],
                ),
            ],
        );
        let whole_real = b.ap(
            "syl2anc",
            &binds! {"ph" => b.wff(&psi), "ps" => b.wff("1 e. RR"),
            "ch" => b.wff(&format!("{inv} e. RR")),
            "th" => b.wff(&format!("( 1 - {inv} ) e. RR"))},
            &[
                &b.ap(
                    "a1i",
                    &binds! {"ph" => b.wff("1 e. RR"), "ps" => b.wff(&psi)},
                    &[&b.step("1re")],
                ),
                &flipped_real,
                &b.ap(
                    "resubcl",
                    &binds! {"A" => b.class("1"), "B" => b.class(&inv)},
                    &[],
                ),
            ],
        );

        // ( C - A ) / ( B - A ) = 1 - ( C - B ) / ( A - B ), in four moves.
        let split = b.ap(
            "syl3anc",
            &binds! {"ph" => b.wff(&psi), "ps" => b.wff(&format!("{ab} e. CC")),
            "ch" => b.wff(&format!("{cb} e. CC")),
            "th" => b.wff(&format!("( {ab} e. CC /\\ {ab} =/= 0 )")),
            "ta" => b.wff(&format!("( ( {ab} - {cb} ) / {ab} ) = ( ( {ab} / {ab} ) - {inv} )"))},
            &[
                &cls[ab],
                &cls[cb],
                &b.ap(
                    "jca",
                    &binds! {"ph" => b.wff(&psi), "ps" => b.wff(&format!("{ab} e. CC")),
                    "ch" => b.wff(&format!("{ab} =/= 0"))},
                    &[&cls[ab], &nz[ab]],
                ),
                &b.ap(
                    "divsubdir",
                    &binds! {"A" => b.class(ab), "B" => b.class(cb), "C" => b.class(ab)},
                    &[],
                ),
            ],
        );
        let cancels = b.ap(
            "oveq1d",
            &binds! {"ph" => b.wff(&psi), "A" => b.class(&format!("( {ab} / {ab} )")),
            "B" => b.class("1"), "C" => b.class(&inv), "F" => b.class("-")},
            &[&b.ap(
                "syl2anc",
                &binds! {"ph" => b.wff(&psi), "ps" => b.wff(&format!("{ab} e. CC")),
                "ch" => b.wff(&format!("{ab} =/= 0")),
                "th" => b.wff(&format!("( {ab} / {ab} ) = 1"))},
                &[
                    &cls[ab],
                    &nz[ab],
                    &b.ap("divid", &binds! {"A" => b.class(ab)}, &[]),
                ],
            )],
        );
        let joins = b.ap(
            "oveq1d",
            &binds! {"ph" => b.wff(&psi), "A" => b.class(&format!("( {ab} - {cb} )")),
            "B" => b.class(ac), "C" => b.class(ab), "F" => b.class("/")},
            &[&b.ap(
                "syl3anc",
                &binds! {"ph" => b.wff(&psi), "ps" => b.wff("A e. CC"),
                "ch" => b.wff("C e. CC"), "th" => b.wff("B e. CC"),
                "ta" => b.wff(&format!("( {ab} - {cb} ) = {ac}"))},
                &[
                    &mem["A"],
                    &mem["C"],
                    &mem["B"],
                    &b.ap(
                        "nnncan2",
                        &binds! {"A" => b.class("A"), "B" => b.class("C"),
                        "C" => b.class("B")},
                        &[],
                    ),
                ],
            )],
        );
        let negated = b.ap(
            "syl3anc",
            &binds! {"ph" => b.wff(&psi), "ps" => b.wff(&format!("{ac} e. CC")),
            "ch" => b.wff(&format!("{ab} e. CC")), "th" => b.wff(&format!("{ab} =/= 0")),
            "ta" => b.wff(&format!("( -u {ac} / -u {ab} ) = ( {ac} / {ab} )"))},
            &[
                &cls[ac],
                &cls[ab],
                &nz[ab],
                &b.ap(
                    "div2neg",
                    &binds! {"A" => b.class(ac), "B" => b.class(ab)},
                    &[],
                ),
            ],
        );
        let turned = b.ap(
            "oveq12d",
            &binds! {"ph" => b.wff(&psi), "A" => b.class(&format!("-u {ac}")),
            "B" => b.class("( C - A )"), "C" => b.class(&format!("-u {ab}")),
            "D" => b.class("( B - A )"), "F" => b.class("/")},
            &[
                &b.ap(
                    "syl2anc",
                    &binds! {"ph" => b.wff(&psi), "ps" => b.wff("A e. CC"),
                    "ch" => b.wff("C e. CC"),
                    "th" => b.wff(&format!("-u {ac} = ( C - A )"))},
                    &[
                        &mem["A"],
                        &mem["C"],
                        &b.ap(
                            "negsubdi2",
                            &binds! {"A" => b.class("A"), "B" => b.class("C")},
                            &[],
                        ),
                    ],
                ),
                &b.ap(
                    "syl2anc",
                    &binds! {"ph" => b.wff(&psi), "ps" => b.wff("A e. CC"),
                    "ch" => b.wff("B e. CC"),
                    "th" => b.wff(&format!("-u {ab} = ( B - A )"))},
                    &[
                        &mem["A"],
                        &mem["B"],
                        &b.ap(
                            "negsubdi2",
                            &binds! {"A" => b.class("A"), "B" => b.class("B")},
                            &[],
                        ),
                    ],
                ),
            ],
        );
        let same = b.ap(
            "3eqtr3d",
            &binds! {"ph" => b.wff(&psi), "A" => b.class(&format!("( -u {ac} / -u {ab} )")),
            "B" => b.class(&format!("( {ac} / {ab} )")), "C" => b.class(goal),
            "D" => b.class(&format!("( 1 - {inv} )"))},
            &[
                &negated,
                &turned,
                &b.ap(
                    "eqtr3d",
                    &binds! {"ph" => b.wff(&psi),
                    "A" => b.class(&format!("( ( {ab} - {cb} ) / {ab} )")),
                    "B" => b.class(&format!("( {ac} / {ab} )")),
                    "C" => b.class(&format!("( 1 - {inv} )"))},
                    &[
                        &joins,
                        &b.ap(
                            "eqtrd",
                            &binds! {"ph" => b.wff(&psi),
                            "A" => b.class(&format!("( ( {ab} - {cb} ) / {ab} )")),
                            "B" => b.class(&format!("( ( {ab} / {ab} ) - {inv} )")),
                            "C" => b.class(&format!("( 1 - {inv} )"))},
                            &[&split, &cancels],
                        ),
                    ],
                ),
            ],
        );
        let reached = b.ap(
            "eqeltrd",
            &binds! {"ph" => b.wff(&psi), "A" => b.class(goal),
            "B" => b.class(&format!("( 1 - {inv} )")),
            "C" => b.class("RR")},
            &[&same, &whole_real],
        );
        out.push(Lemma::new(
            "gtricol",
            says.clone(),
            b.ap(
                "ex",
                &binds! {"ph" => b.wff(&ph), "ps" => b.wff(&format!("{quo} e. RR")),
                "ch" => b.wff(&format!("{goal} e. RR"))},
                &[&reached],
            ),
        ));
    }
    b.define("gtricol", &says);
    let b: &Builder = b;

    // Rotating all three vertices, which the isosceles proof cites once.
    let points = "( A e. CC /\\ B e. CC /\\ C e. CC )";
    let (given, want) = (triangle("A", "B", "C"), triangle("B", "C", "A"));
    let held = format!("( {points} /\\ {given} )");
    let mem = members(b, points, &given);
    let inner = "( ( -. A = B /\\ -. B = C ) /\\ -. A = C )";
    let straightness = "-. ( ( C - A ) / ( B - A ) ) e. RR";
    let whole = b.ap(
        "simpr",
        &binds! {"ph" => b.wff(points), "ps" => b.wff(&given)},
        &[],
    );
    let apart_of = binds! {"ph" => b.wff(&held), "ps" => b.wff(inner),
    "ch" => b.wff(straightness)};
    let distinct = b.ap("simpld", &apart_of, &[&whole]);
    let straight = b.ap("simprd", &apart_of, &[&whole]);
    let pair_of = binds! {"ph" => b.wff(&held), "ps" => b.wff("( -. A = B /\\ -. B = C )"),
    "ch" => b.wff("-. A = C")};
    let pair = b.ap("simpld", &pair_of, &[&distinct]);
    let not_ac = b.ap("simprd", &pair_of, &[&distinct]);
    let two_of = binds! {"ph" => b.wff(&held), "ps" => b.wff("-. A = B"),
    "ch" => b.wff("-. B = C")};
    let not_ab = b.ap("simpld", &two_of, &[&pair]);
    let not_bc = b.ap("simprd", &two_of, &[&pair]);

    let turned = b.ap(
        "mpd",
        &binds! {"ph" => b.wff(&held), "ps" => b.wff(straightness),
        "ch" => b.wff(&format!("-. {quo} e. RR"))},
        &[
            &straight,
            &b.ap(
                "con3d",
                &binds! {"ph" => b.wff(&held), "ps" => b.wff(&format!("{quo} e. RR")),
                "ch" => b.wff(&format!("{goal} e. RR"))},
                &[&b.ap(
                    "syl",
                    &binds! {"ph" => b.wff(&held), "ps" => b.wff(&ph),
                    "ch" => b.wff(&format!("( {quo} e. RR -> {goal} e. RR )"))},
                    &[
                        &b.ap(
                            "jca",
                            &binds! {"ph" => b.wff(&held), "ps" => b.wff(points),
                            "ch" => b.wff(apart)},
                            &[
                                &b.ap(
                                    "simpl",
                                    &binds! {"ph" => b.wff(points),
                                    "ps" => b.wff(&given)},
                                    &[],
                                ),
                                &b.ap(
                                    "jca",
                                    &binds! {"ph" => b.wff(&held),
                                    "ps" => b.wff(&format!("{ab} =/= 0")),
                                    "ch" => b.wff(&format!("{cb} =/= 0"))},
                                    &[
                                        &differs(
                                            b, &held, "A", "B", &mem["A"], &mem["B"],
                                            &not_ab,
                                        ),
                                        &differs(
                                            b,
                                            &held,
                                            "C",
                                            "B",
                                            &mem["C"],
                                            &mem["B"],
                                            &flipped(b, &held, "B", "C", &not_bc),
                                        ),
                                    ],
                                ),
                            ],
                        ),
                        &b.ap("gtricol", &binds! {}, &[]),
                    ],
                )],
            ),
        ],
    );
    let built = b.ap(
        "jca",
        &binds! {"ph" => b.wff(&held),
        "ps" => b.wff("( ( -. B = C /\\ -. C = A ) /\\ -. B = A )"),
        "ch" => b.wff(&format!("-. {quo} e. RR"))},
        &[
            &b.ap(
                "jca31",
                &binds! {"ph" => b.wff(&held), "ps" => b.wff("-. B = C"),
                "ch" => b.wff("-. C = A"), "th" => b.wff("-. B = A")},
                &[
                    &not_bc,
                    &flipped(b, &held, "A", "C", &not_ac),
                    &flipped(b, &held, "A", "B", &not_ab),
                ],
            ),
            &turned,
        ],
    );
    out.push(Lemma::new(
        "gtrirotate",
        format!("|- ( {points} -> ( {given} -> {want} ) )"),
        b.ap(
            "ex",
            &binds! {"ph" => b.wff(points), "ps" => b.wff(&given),
            "ch" => b.wff(&want)},
            &[&built],
        ),
    ));
}

/// Three points with the middle one apart from the other two, and the two
/// differences from it nonzero numbers, which is what a lemma about the
/// signed angle asks of them.
///
/// Gives the points, the apartness, the two together, the differences, and
/// ( held -> ( ( A - B ) e. CC /\ ( A - B ) =/= 0 ) /\ ( ... ) ).
struct SidesApart {
    points: &'static str,
    apart: &'static str,
    held: String,
    ab: &'static str,
    cb: &'static str,
    ready: Proof,
}

fn sides_apart(b: &Builder) -> SidesApart {
    let points = "( A e. CC /\\ B e. CC /\\ C e. CC )";
    let apart = "( -. A = B /\\ -. C = B )";
    let held = format!("( {points} /\\ {apart} )");
    let (ab, cb) = ("( A - B )", "( C - B )");
    let mem = members(b, points, apart);
    let two = binds! {"ph" => b.wff("-. A = B"), "ps" => b.wff("-. C = B")};
    let mut unequal: IndexMap<&str, Proof> = IndexMap::new();
    for (name, pick) in [("AB", "simpl"), ("CB", "simpr")] {
        unequal.insert(
            name,
            b.ap(
                "adantl",
                &binds! {"ph" => b.wff(apart),
                "ps" => b.wff(if name == "AB" { "-. A = B" } else { "-. C = B" }),
                "ch" => b.wff(points)},
                &[&b.ap(pick, &two, &[])],
            ),
        );
    }
    let ready = b.ap(
        "jca",
        &binds! {"ph" => b.wff(&held),
        "ps" => b.wff(&format!("( {ab} e. CC /\\ {ab} =/= 0 )")),
        "ch" => b.wff(&format!("( {cb} e. CC /\\ {cb} =/= 0 )"))},
        &[
            &b.ap(
                "jca",
                &binds! {"ph" => b.wff(&held), "ps" => b.wff(&format!("{ab} e. CC")),
                "ch" => b.wff(&format!("{ab} =/= 0"))},
                &[
                    &b.ap(
                        "subcld",
                        &binds! {"ph" => b.wff(&held), "A" => b.class("A"),
                        "B" => b.class("B")},
                        &[&mem["A"], &mem["B"]],
                    ),
                    &differs(b, &held, "A", "B", &mem["A"], &mem["B"], &unequal["AB"]),
                ],
            ),
            &b.ap(
                "jca",
                &binds! {"ph" => b.wff(&held), "ps" => b.wff(&format!("{cb} e. CC")),
                "ch" => b.wff(&format!("{cb} =/= 0"))},
                &[
                    &b.ap(
                        "subcld",
                        &binds! {"ph" => b.wff(&held), "A" => b.class("C"),
                        "B" => b.class("B")},
                        &[&mem["C"], &mem["B"]],
                    ),
                    &differs(b, &held, "C", "B", &mem["C"], &mem["B"], &unequal["CB"]),
                ],
            ),
        ],
    );
    SidesApart {
        points,
        apart,
        held,
        ab,
        cb,
        ready,
    }
}

/// The angle from A to B and the angle from B to A have one size.
///
/// `ang` is signed and lands in −pi to pi, so the two are not equal; the
/// corpus writes the unsigned angle, which is this one's absolute value, and
/// those do agree. Off the branch cut that is `arginv`, which says the signed
/// angle of an inverse is the negative of the angle. On the cut `arginv`
/// does not apply and nothing is negated: `lognegb` says a number whose
/// negative is a positive real has angle pi exactly, and the inverse of such
/// a number is another, so both angles are pi.
fn angle_symmetry(b: &mut Builder, out: &mut Vec<Lemma>) {
    let ph = "( ( A e. CC /\\ A =/= 0 ) /\\ ( B e. CC /\\ B =/= 0 ) )";
    let (z, rz) = ("( B / A )", "( 1 / ( B / A ) )");
    let (theta, rtheta) = (
        format!("( Im ` ( log ` {z} ) )"),
        format!("( Im ` ( log ` {rz} ) )"),
    );
    let cut = format!("-u {z} e. RR+");

    let (value, swapped, z_cc, z_nz) = {
        let b: &Builder = b;
        let left = b.ap(
            "simpl",
            &binds! {"ph" => b.wff("( A e. CC /\\ A =/= 0 )"),
            "ps" => b.wff("( B e. CC /\\ B =/= 0 )")},
            &[],
        );
        let right = b.ap(
            "simpr",
            &binds! {"ph" => b.wff("( A e. CC /\\ A =/= 0 )"),
            "ps" => b.wff("( B e. CC /\\ B =/= 0 )")},
            &[],
        );
        let mut part: IndexMap<&str, Proof> = IndexMap::new();
        for (name, is_left, which) in [
            ("Acc", true, "simpld"),
            ("Anz", true, "simprd"),
            ("Bcc", false, "simpld"),
            ("Bnz", false, "simprd"),
        ] {
            let one = if is_left { "A" } else { "B" };
            let whole = if is_left { &left } else { &right };
            part.insert(
                name,
                b.ap(
                    which,
                    &binds! {"ph" => b.wff(ph),
                    "ps" => b.wff(&format!("{one} e. CC")),
                    "ch" => b.wff(&format!("{one} =/= 0"))},
                    &[whole],
                ),
            );
        }
        let z_cc = b.ap(
            "syl3anc",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff("B e. CC"),
            "ch" => b.wff("A e. CC"), "th" => b.wff("A =/= 0"),
            "ta" => b.wff(&format!("{z} e. CC"))},
            &[
                &part["Bcc"],
                &part["Acc"],
                &part["Anz"],
                &b.ap(
                    "divcl",
                    &binds! {"A" => b.class("B"), "B" => b.class("A")},
                    &[],
                ),
            ],
        );
        let z_nz = b.ap(
            "syl",
            &binds! {"ph" => b.wff(ph),
            "ps" => b.wff("( ( B e. CC /\\ B =/= 0 ) /\\ ( A e. CC /\\ A =/= 0 ) )"),
            "ch" => b.wff(&format!("{z} =/= 0"))},
            &[
                &b.ap(
                    "jca",
                    &binds! {"ph" => b.wff(ph),
                    "ps" => b.wff("( B e. CC /\\ B =/= 0 )"),
                    "ch" => b.wff("( A e. CC /\\ A =/= 0 )")},
                    &[&right, &left],
                ),
                &b.ap(
                    "divne0",
                    &binds! {"A" => b.class("B"), "B" => b.class("A")},
                    &[],
                ),
            ],
        );

        // ( A ang B ) is the angle of B / A, and ( B ang A ) that of its
        // inverse.
        let value = b.ap(
            "angval",
            &binds! {"A" => b.class("A"), "B" => b.class("B"),
            "F" => b.class("ang")},
            &[&b.ap("df-ang", &binds! {}, &[])],
        );
        let other = "( Im ` ( log ` ( A / B ) ) )";
        let flipped_ph = "( ( B e. CC /\\ B =/= 0 ) /\\ ( A e. CC /\\ A =/= 0 ) )";
        let other_way = b.ap(
            "jca",
            &binds! {"ph" => b.wff(ph),
            "ps" => b.wff("( B e. CC /\\ B =/= 0 )"),
            "ch" => b.wff("( A e. CC /\\ A =/= 0 )")},
            &[&right, &left],
        );
        // A / B is the inverse of B / A, so the second angle is the angle of
        // the inverse and the two lemmas below are about one number.
        let inverts = b.ap(
            "eqcomd",
            &binds! {"ph" => b.wff(ph), "A" => b.class(rz),
            "B" => b.class("( A / B )")},
            &[&b.ap(
                "syl",
                &binds! {"ph" => b.wff(ph), "ps" => b.wff(flipped_ph),
                "ch" => b.wff(&format!("{rz} = ( A / B )"))},
                &[
                    &other_way,
                    &b.ap(
                        "recdiv",
                        &binds! {"A" => b.class("B"), "B" => b.class("A")},
                        &[],
                    ),
                ],
            )],
        );
        let reads = b.ap(
            "fveq2d",
            &binds! {"ph" => b.wff(ph),
            "A" => b.class("( log ` ( A / B ) )"),
            "B" => b.class(&format!("( log ` {rz} )")), "F" => b.class("Im")},
            &[&b.ap(
                "fveq2d",
                &binds! {"ph" => b.wff(ph), "A" => b.class("( A / B )"),
                "B" => b.class(rz), "F" => b.class("log")},
                &[&inverts],
            )],
        );
        let swapped = b.ap(
            "eqtrd",
            &binds! {"ph" => b.wff(ph), "A" => b.class("( B ang A )"),
            "B" => b.class(other), "C" => b.class(&rtheta)},
            &[
                &b.ap(
                    "ancoms",
                    &binds! {"ph" => b.wff("( B e. CC /\\ B =/= 0 )"),
                    "ps" => b.wff("( A e. CC /\\ A =/= 0 )"),
                    "ch" => b.wff(&format!("( B ang A ) = {other}"))},
                    &[&b.ap(
                        "angval",
                        &binds! {"A" => b.class("B"), "B" => b.class("A"),
                        "F" => b.class("ang")},
                        &[&b.ap("df-ang", &binds! {}, &[])],
                    )],
                ),
                &reads,
            ],
        );
        (value, swapped, z_cc, z_nz)
    };
    for (label, says, proof) in [
        (
            "gangval",
            format!("|- ( {ph} -> ( A ang B ) = {theta} )"),
            value.clone(),
        ),
        (
            "gangrec",
            format!("|- ( {ph} -> ( B ang A ) = {rtheta} )"),
            swapped.clone(),
        ),
    ] {
        out.push(Lemma::new(label, says.clone(), proof));
        b.define(label, &says);
    }

    let says = format!("|- ( {ph} -> ( abs ` ( A ang B ) ) = ( abs ` ( B ang A ) ) ) ");
    let says = says.trim().to_string();
    {
        let b: &Builder = b;
        // Off the branch cut the two angles are negatives of one another,
        // and an absolute value does not tell them apart.
        let off = format!("( {ph} /\\ -. {cut} )");
        let free = b.ap(
            "fveq2d",
            &binds! {"ph" => b.wff(&off), "A" => b.class(&rtheta),
            "B" => b.class(&format!("-u {theta}")), "F" => b.class("abs")},
            &[&b.ap(
                "arginv",
                &binds! {"ph" => b.wff(&off), "A" => b.class(z)},
                &[
                    &b.ap(
                        "adantr",
                        &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{z} e. CC")),
                        "ch" => b.wff(&format!("-. {cut}"))},
                        &[&z_cc],
                    ),
                    &b.ap(
                        "adantr",
                        &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{z} =/= 0")),
                        "ch" => b.wff(&format!("-. {cut}"))},
                        &[&z_nz],
                    ),
                    &b.ap(
                        "simpr",
                        &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("-. {cut}"))},
                        &[],
                    ),
                ],
            )],
        );
        let angle_cc = b.ap(
            "syl",
            &binds! {"ph" => b.wff(&off), "ps" => b.wff(&format!("{theta} e. RR")),
            "ch" => b.wff(&format!("{theta} e. CC"))},
            &[
                &b.ap(
                    "syl",
                    &binds! {"ph" => b.wff(&off), "ps" => b.wff(&format!("( log ` {z} ) e. CC")),
                    "ch" => b.wff(&format!("{theta} e. RR"))},
                    &[
                        &b.ap(
                            "logcld",
                            &binds! {"ph" => b.wff(&off), "X" => b.class(z)},
                            &[
                                &b.ap(
                                    "adantr",
                                    &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{z} e. CC")),
                                    "ch" => b.wff(&format!("-. {cut}"))},
                                    &[&z_cc],
                                ),
                                &b.ap(
                                    "adantr",
                                    &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{z} =/= 0")),
                                    "ch" => b.wff(&format!("-. {cut}"))},
                                    &[&z_nz],
                                ),
                            ],
                        ),
                        &b.ap(
                            "imcl",
                            &binds! {"A" => b.class(&format!("( log ` {z} )"))},
                            &[],
                        ),
                    ],
                ),
                &b.ap("recn", &binds! {"A" => b.class(&theta)}, &[]),
            ],
        );
        let outside = b.ap(
            "eqcomd",
            &binds! {"ph" => b.wff(&off), "A" => b.class(&format!("( abs ` {rtheta} )")),
            "B" => b.class(&format!("( abs ` {theta} )"))},
            &[&b.ap(
                "eqtrd",
                &binds! {"ph" => b.wff(&off), "A" => b.class(&format!("( abs ` {rtheta} )")),
                "B" => b.class(&format!("( abs ` -u {theta} )")),
                "C" => b.class(&format!("( abs ` {theta} )"))},
                &[
                    &free,
                    &b.ap(
                        "syl",
                        &binds! {"ph" => b.wff(&off), "ps" => b.wff(&format!("{theta} e. CC")),
                        "ch" => b.wff(&format!("( abs ` -u {theta} ) = ( abs ` {theta} )"))},
                        &[&angle_cc, &b.ap("absneg", &binds! {"A" => b.class(&theta)}, &[])],
                    ),
                ],
            )],
        );

        // On the cut neither angle is negated: both are pi exactly.
        let on = format!("( {ph} /\\ {cut} )");
        let is_pi = |what: &str,
                     whole: &Proof,
                     nonzero: &Proof,
                     positive: &Proof|
         -> Proof {
            b.ap(
                "mpbid",
                &binds! {"ph" => b.wff(&on), "ps" => b.wff(&format!("-u {what} e. RR+")),
                "ch" => b.wff(&format!("( Im ` ( log ` {what} ) ) = _pi"))},
                &[
                    positive,
                    &b.ap(
                        "syl2anc",
                        &binds! {"ph" => b.wff(&on),
                        "ps" => b.wff(&format!("{what} e. CC")),
                        "ch" => b.wff(&format!("{what} =/= 0")),
                        "th" => b.wff(&format!("( -u {what} e. RR+ <-> ( Im ` ( log ` {what} ) ) = _pi )"))},
                        &[
                            whole,
                            nonzero,
                            &b.ap("lognegb", &binds! {"A" => b.class(what)}, &[]),
                        ],
                    ),
                ],
            )
        };

        let z_cc_on = b.ap(
            "adantr",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{z} e. CC")),
            "ch" => b.wff(&cut)},
            &[&z_cc],
        );
        let z_nz_on = b.ap(
            "adantr",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{z} =/= 0")),
            "ch" => b.wff(&cut)},
            &[&z_nz],
        );
        let held = b.ap(
            "simpr",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff(&cut)},
            &[],
        );
        // -u ( 1 / z ) is ( 1 / -u z ), and the reciprocal of a positive real
        // is one, so the inverse sits on the cut whenever z does.
        let rz_positive = b.ap(
            "eqeltrrd",
            &binds! {"ph" => b.wff(&on), "A" => b.class(&format!("( 1 / -u {z} )")),
            "B" => b.class(&format!("-u {rz}")), "C" => b.class("RR+")},
            &[
                &b.ap(
                    "eqcomd",
                    &binds! {"ph" => b.wff(&on), "A" => b.class(&format!("-u {rz}")),
                    "B" => b.class(&format!("( 1 / -u {z} )"))},
                    &[&b.ap(
                        "syl3anc",
                        &binds! {"ph" => b.wff(&on), "ps" => b.wff("1 e. CC"),
                        "ch" => b.wff(&format!("{z} e. CC")), "th" => b.wff(&format!("{z} =/= 0")),
                        "ta" => b.wff(&format!("-u {rz} = ( 1 / -u {z} )"))},
                        &[
                            &b.ap(
                                "a1i",
                                &binds! {"ph" => b.wff("1 e. CC"), "ps" => b.wff(&on)},
                                &[&b.step("ax-1cn")],
                            ),
                            &z_cc_on,
                            &z_nz_on,
                            &b.ap("divneg2", &binds! {"A" => b.class("1"), "B" => b.class(z)}, &[]),
                        ],
                    )],
                ),
                &b.ap(
                    "syl",
                    &binds! {"ph" => b.wff(&on), "ps" => b.wff(&format!("-u {z} e. RR+")),
                    "ch" => b.wff(&format!("( 1 / -u {z} ) e. RR+"))},
                    &[
                        &held,
                        &b.ap("rpreccl", &binds! {"A" => b.class(&format!("-u {z}"))}, &[]),
                    ],
                ),
            ],
        );
        let inside = b.ap(
            "eqtr4d",
            &binds! {"ph" => b.wff(&on), "A" => b.class(&format!("( abs ` {theta} )")),
            "B" => b.class("( abs ` _pi )"),
            "C" => b.class(&format!("( abs ` {rtheta} )"))},
            &[
                &b.ap(
                    "fveq2d",
                    &binds! {"ph" => b.wff(&on), "A" => b.class(&theta),
                    "B" => b.class("_pi"), "F" => b.class("abs")},
                    &[&is_pi(z, &z_cc_on, &z_nz_on, &held)],
                ),
                &b.ap(
                    "fveq2d",
                    &binds! {"ph" => b.wff(&on), "A" => b.class(&rtheta),
                    "B" => b.class("_pi"), "F" => b.class("abs")},
                    &[&is_pi(
                        rz,
                        &b.ap(
                            "reccld",
                            &binds! {"ph" => b.wff(&on), "A" => b.class(z)},
                            &[&z_cc_on, &z_nz_on],
                        ),
                        &b.ap(
                            "recne0d",
                            &binds! {"ph" => b.wff(&on), "A" => b.class(z)},
                            &[&z_cc_on, &z_nz_on],
                        ),
                        &rz_positive,
                    )],
                ),
            ],
        );

        let joined = b.ap(
            "pm2.61dan",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff(&cut),
            "ch" => b.wff(&format!("( abs ` {theta} ) = ( abs ` {rtheta} )"))},
            &[&inside, &outside],
        );
        let whole = b.ap(
            "3eqtr4d",
            &binds! {"ph" => b.wff(ph), "A" => b.class(&format!("( abs ` {theta} )")),
            "B" => b.class(&format!("( abs ` {rtheta} )")),
            "C" => b.class("( abs ` ( A ang B ) )"),
            "D" => b.class("( abs ` ( B ang A ) )")},
            &[
                &joined,
                &b.ap(
                    "fveq2d",
                    &binds! {"ph" => b.wff(ph), "A" => b.class("( A ang B )"),
                    "B" => b.class(&theta), "F" => b.class("abs")},
                    &[&value],
                ),
                &b.ap(
                    "fveq2d",
                    &binds! {"ph" => b.wff(ph), "A" => b.class("( B ang A )"),
                    "B" => b.class(&rtheta), "F" => b.class("abs")},
                    &[&swapped],
                ),
            ],
        );
        out.push(Lemma::new("gangsym", says.clone(), whole));
    }
    b.define("gangsym", &says);
    let b: &Builder = b;

    // The same on three points, which is how the corpus states it: the angle
    // at B is between the two differences, and each is nonzero because B is
    // neither of the other two.
    let s = sides_apart(b);
    let (ab, cb) = (s.ab, s.cb);
    let claim = format!("( abs ` ( {ab} ang {cb} ) ) = ( abs ` ( {cb} ang {ab} ) )");
    out.push(Lemma::new(
        "gangsym3",
        format!("|- ( {} -> ( {} -> {claim} ) )", s.points, s.apart),
        b.ap(
            "ex",
            &binds! {"ph" => b.wff(s.points), "ps" => b.wff(s.apart),
            "ch" => b.wff(&claim)},
            &[&b.ap(
                "syl",
                &binds! {"ph" => b.wff(&s.held),
                "ps" => b.wff(&format!("( ( {ab} e. CC /\\ {ab} =/= 0 ) /\\ ( {cb} e. CC /\\ {cb} =/= 0 ) )")),
                "ch" => b.wff(&claim)},
                &[
                    &s.ready,
                    &b.ap("gangsym", &binds! {"A" => b.class(ab), "B" => b.class(cb)}, &[]),
                ],
            )],
        ),
    ));
}

/// Where the unsigned angle lives, and what cosine makes of it.
///
/// Two facts the law of cosines needs. `lawcos` states itself with the
/// signed angle, and the corpus writes the unsigned one, so a step that
/// carries an angle between the two has to know that cosine cannot tell them
/// apart, and that going back is possible because cosine is one to one on
/// the range the unsigned angle occupies.
fn angle_size(b: &mut Builder, out: &mut Vec<Lemma>) {
    // Cosine is even, so it reads an absolute value and the sign it lost.
    let real = "A e. RR";
    let same = "( cos ` ( abs ` A ) ) = ( cos ` A )";
    let says = format!("|- ( {real} -> {same} )");
    {
        let b: &Builder = b;
        let proof = b.ap(
            "lecasei",
            &binds! {"ph" => b.wff(real), "ps" => b.wff(same), "A" => b.class("0"),
            "B" => b.class("A")},
            &[
                &b.ap(
                    "a1i",
                    &binds! {"ph" => b.wff("0 e. RR"), "ps" => b.wff(real)},
                    &[&b.step("0re")],
                ),
                &b.ap("id", &binds! {"ph" => b.wff(real)}, &[]),
                &b.ap(
                    "fveq2d",
                    &binds! {"ph" => b.wff(&format!("( {real} /\\ 0 <_ A )")),
                    "A" => b.class("( abs ` A )"), "B" => b.class("A"),
                    "F" => b.class("cos")},
                    &[&b.ap("absid", &binds! {"A" => b.class("A")}, &[])],
                ),
                &b.ap(
                    "eqtrd",
                    &binds! {"ph" => b.wff(&format!("( {real} /\\ A <_ 0 )")),
                    "A" => b.class("( cos ` ( abs ` A ) )"),
                    "B" => b.class("( cos ` -u A )"),
                    "C" => b.class("( cos ` A )")},
                    &[
                        &b.ap(
                            "fveq2d",
                            &binds! {"ph" => b.wff(&format!("( {real} /\\ A <_ 0 )")),
                            "A" => b.class("( abs ` A )"), "B" => b.class("-u A"),
                            "F" => b.class("cos")},
                            &[&b.ap("absnid", &binds! {"A" => b.class("A")}, &[])],
                        ),
                        &b.ap(
                            "syl",
                            &binds! {"ph" => b.wff(&format!("( {real} /\\ A <_ 0 )")),
                            "ps" => b.wff("A e. CC"),
                            "ch" => b.wff("( cos ` -u A ) = ( cos ` A )")},
                            &[
                                &b.ap(
                                    "recnd",
                                    &binds! {"ph" => b.wff(&format!("( {real} /\\ A <_ 0 )")),
                                    "A" => b.class("A")},
                                    &[&b.ap(
                                        "simpl",
                                        &binds! {"ph" => b.wff(real),
                                        "ps" => b.wff("A <_ 0")},
                                        &[],
                                    )],
                                ),
                                &b.ap("cosneg", &binds! {"A" => b.class("A")}, &[]),
                            ],
                        ),
                    ],
                ),
            ],
        );
        out.push(Lemma::new("gcosabs", says.clone(), proof));
    }
    b.define("gcosabs", &says);

    // The signed angle sits in -pi to pi, half-open at the bottom, so the
    // unsigned one sits in 0 to pi and `cos11` applies to it.
    let ph = "( ( A e. CC /\\ A =/= 0 ) /\\ ( B e. CC /\\ B =/= 0 ) )";
    let z = "( B / A )";
    let theta = format!("( Im ` ( log ` {z} ) )");
    let size = "( abs ` ( A ang B ) )";
    let says = format!("|- ( {ph} -> {size} e. ( 0 [,] _pi ) )");
    {
        let b: &Builder = b;
        let left = b.ap(
            "simpl",
            &binds! {"ph" => b.wff("( A e. CC /\\ A =/= 0 )"),
            "ps" => b.wff("( B e. CC /\\ B =/= 0 )")},
            &[],
        );
        let right = b.ap(
            "simpr",
            &binds! {"ph" => b.wff("( A e. CC /\\ A =/= 0 )"),
            "ps" => b.wff("( B e. CC /\\ B =/= 0 )")},
            &[],
        );
        let z_cc = b.ap(
            "syl3anc",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff("B e. CC"),
            "ch" => b.wff("A e. CC"), "th" => b.wff("A =/= 0"),
            "ta" => b.wff(&format!("{z} e. CC"))},
            &[
                &b.ap(
                    "simpld",
                    &binds! {"ph" => b.wff(ph), "ps" => b.wff("B e. CC"),
                    "ch" => b.wff("B =/= 0")},
                    &[&right],
                ),
                &b.ap(
                    "simpld",
                    &binds! {"ph" => b.wff(ph), "ps" => b.wff("A e. CC"),
                    "ch" => b.wff("A =/= 0")},
                    &[&left],
                ),
                &b.ap(
                    "simprd",
                    &binds! {"ph" => b.wff(ph), "ps" => b.wff("A e. CC"),
                    "ch" => b.wff("A =/= 0")},
                    &[&left],
                ),
                &b.ap(
                    "divcl",
                    &binds! {"A" => b.class("B"), "B" => b.class("A")},
                    &[],
                ),
            ],
        );
        let z_nz = b.ap(
            "syl",
            &binds! {"ph" => b.wff(ph),
            "ps" => b.wff("( ( B e. CC /\\ B =/= 0 ) /\\ ( A e. CC /\\ A =/= 0 ) )"),
            "ch" => b.wff(&format!("{z} =/= 0"))},
            &[
                &b.ap(
                    "jca",
                    &binds! {"ph" => b.wff(ph),
                    "ps" => b.wff("( B e. CC /\\ B =/= 0 )"),
                    "ch" => b.wff("( A e. CC /\\ A =/= 0 )")},
                    &[&right, &left],
                ),
                &b.ap(
                    "divne0",
                    &binds! {"A" => b.class("B"), "B" => b.class("A")},
                    &[],
                ),
            ],
        );
        let bounds = b.ap(
            "syl2anc",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{z} e. CC")),
            "ch" => b.wff(&format!("{z} =/= 0")),
            "th" => b.wff(&format!("( -u _pi < {theta} /\\ {theta} <_ _pi )"))},
            &[
                &z_cc,
                &z_nz,
                &b.ap("logimcl", &binds! {"A" => b.class(z)}, &[]),
            ],
        );
        let theta_re = b.ap(
            "imcld",
            &binds! {"ph" => b.wff(ph), "A" => b.class(&format!("( log ` {z} )"))},
            &[&b.ap(
                "logcld",
                &binds! {"ph" => b.wff(ph), "X" => b.class(z)},
                &[&z_cc, &z_nz],
            )],
        );
        // -pi < theta gives -pi <_ theta, which is the half `absle` wants.
        let under = b.ap(
            "mpbir2and",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("( abs ` {theta} ) <_ _pi")),
            "ch" => b.wff(&format!("-u _pi <_ {theta}")),
            "th" => b.wff(&format!("{theta} <_ _pi"))},
            &[
                &b.ap(
                    "ltled",
                    &binds! {"ph" => b.wff(ph), "A" => b.class("-u _pi"),
                    "B" => b.class(&theta)},
                    &[
                        &b.ap(
                            "a1i",
                            &binds! {"ph" => b.wff("-u _pi e. RR"),
                            "ps" => b.wff(ph)},
                            &[&b.ap(
                                "ax-mp",
                                &binds! {"ph" => b.wff("_pi e. RR"),
                                "ps" => b.wff("-u _pi e. RR")},
                                &[
                                    &b.step("pire"),
                                    &b.ap("renegcl", &binds! {"A" => b.class("_pi")}, &[]),
                                ],
                            )],
                        ),
                        &theta_re,
                        &b.ap(
                            "simpld",
                            &binds! {"ph" => b.wff(ph),
                            "ps" => b.wff(&format!("-u _pi < {theta}")),
                            "ch" => b.wff(&format!("{theta} <_ _pi"))},
                            &[&bounds],
                        ),
                    ],
                ),
                &b.ap(
                    "simprd",
                    &binds! {"ph" => b.wff(ph),
                    "ps" => b.wff(&format!("-u _pi < {theta}")),
                    "ch" => b.wff(&format!("{theta} <_ _pi"))},
                    &[&bounds],
                ),
                &b.ap(
                    "syl2anc",
                    &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{theta} e. RR")),
                    "ch" => b.wff("_pi e. RR"),
                    "th" => b.wff(&format!("( ( abs ` {theta} ) <_ _pi <-> ( -u _pi <_ {theta} /\\ {theta} <_ _pi ) )"))},
                    &[
                        &theta_re,
                        &b.ap(
                            "a1i",
                            &binds! {"ph" => b.wff("_pi e. RR"),
                            "ps" => b.wff(ph)},
                            &[&b.step("pire")],
                        ),
                        &b.ap(
                            "absle",
                            &binds! {"A" => b.class(&theta), "B" => b.class("_pi")},
                            &[],
                        ),
                    ],
                ),
            ],
        );
        let lands = b.ap(
            "mpbir3and",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("( abs ` {theta} ) e. ( 0 [,] _pi )")),
            "ch" => b.wff(&format!("( abs ` {theta} ) e. RR")),
            "th" => b.wff(&format!("0 <_ ( abs ` {theta} )")),
            "ta" => b.wff(&format!("( abs ` {theta} ) <_ _pi"))},
            &[
                &b.ap(
                    "syl",
                    &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{theta} e. CC")),
                    "ch" => b.wff(&format!("( abs ` {theta} ) e. RR"))},
                    &[
                        &b.ap(
                            "recnd",
                            &binds! {"ph" => b.wff(ph), "A" => b.class(&theta)},
                            &[&theta_re],
                        ),
                        &b.ap("abscl", &binds! {"A" => b.class(&theta)}, &[]),
                    ],
                ),
                &b.ap(
                    "syl",
                    &binds! {"ph" => b.wff(ph), "ps" => b.wff(&format!("{theta} e. CC")),
                    "ch" => b.wff(&format!("0 <_ ( abs ` {theta} )"))},
                    &[
                        &b.ap(
                            "recnd",
                            &binds! {"ph" => b.wff(ph), "A" => b.class(&theta)},
                            &[&theta_re],
                        ),
                        &b.ap("absge0", &binds! {"A" => b.class(&theta)}, &[]),
                    ],
                ),
                &under,
                &b.ap(
                    "syl2anc",
                    &binds! {"ph" => b.wff(ph), "ps" => b.wff("0 e. RR"),
                    "ch" => b.wff("_pi e. RR"),
                    "th" => b.wff(&format!("( ( abs ` {theta} ) e. ( 0 [,] _pi ) <-> ( ( abs ` {theta} ) e. RR /\\ 0 <_ ( abs ` {theta} ) /\\ ( abs ` {theta} ) <_ _pi ) )"))},
                    &[
                        &b.ap(
                            "a1i",
                            &binds! {"ph" => b.wff("0 e. RR"), "ps" => b.wff(ph)},
                            &[&b.step("0re")],
                        ),
                        &b.ap(
                            "a1i",
                            &binds! {"ph" => b.wff("_pi e. RR"), "ps" => b.wff(ph)},
                            &[&b.step("pire")],
                        ),
                        &b.ap(
                            "elicc2",
                            &binds! {"A" => b.class("0"), "B" => b.class("_pi"),
                            "C" => b.class(&format!("( abs ` {theta} )"))},
                            &[],
                        ),
                    ],
                ),
            ],
        );
        let proof = b.ap(
            "eqeltrd",
            &binds! {"ph" => b.wff(ph), "A" => b.class(size),
            "B" => b.class(&format!("( abs ` {theta} )")),
            "C" => b.class("( 0 [,] _pi )")},
            &[
                &b.ap(
                    "fveq2d",
                    &binds! {"ph" => b.wff(ph), "A" => b.class("( A ang B )"),
                    "B" => b.class(&theta), "F" => b.class("abs")},
                    &[&b.ap(
                        "gangval",
                        &binds! {"A" => b.class("A"), "B" => b.class("B")},
                        &[],
                    )],
                ),
                &lands,
            ],
        );
        out.push(Lemma::new("gangrange", says.clone(), proof));
    }
    b.define("gangrange", &says);
}

/// The unsigned angle on three points is real and at least 0.
///
/// What `mun:stdlib/geometry/angle-real` says, stated as the corpus states an
/// angle: at B, between the two differences, B apart from the other two. It
/// is the first two of the three things `gangrange` says, read off the
/// closed interval by `elicc2`.
fn angle_bounds(b: &Builder, out: &mut Vec<Lemma>) {
    let s = sides_apart(b);
    let (ab, cb, held) = (s.ab, s.cb, &s.held);
    let size = format!("( abs ` ( {ab} ang {cb} ) )");
    let both = format!("( {size} e. RR /\\ 0 <_ {size} )");
    let three = format!("( {size} e. RR /\\ 0 <_ {size} /\\ {size} <_ _pi )");
    let inside = b.ap(
        "syl",
        &binds! {"ph" => b.wff(held),
        "ps" => b.wff(&format!("( ( {ab} e. CC /\\ {ab} =/= 0 ) /\\ ( {cb} e. CC /\\ {cb} =/= 0 ) )")),
        "ch" => b.wff(&format!("{size} e. ( 0 [,] _pi )"))},
        &[
            &s.ready,
            &b.ap("gangrange", &binds! {"A" => b.class(ab), "B" => b.class(cb)}, &[]),
        ],
    );
    let spelt = b.ap(
        "mpbid",
        &binds! {"ph" => b.wff(held),
        "ps" => b.wff(&format!("{size} e. ( 0 [,] _pi )")),
        "ch" => b.wff(&three)},
        &[
            &inside,
            &b.ap(
                "syl2anc",
                &binds! {"ph" => b.wff(held), "ps" => b.wff("0 e. RR"),
                "ch" => b.wff("_pi e. RR"),
                "th" => b.wff(&format!("( {size} e. ( 0 [,] _pi ) <-> {three} )"))},
                &[
                    &b.ap(
                        "a1i",
                        &binds! {"ph" => b.wff("0 e. RR"), "ps" => b.wff(held)},
                        &[&b.step("0re")],
                    ),
                    &b.ap(
                        "a1i",
                        &binds! {"ph" => b.wff("_pi e. RR"), "ps" => b.wff(held)},
                        &[&b.step("pire")],
                    ),
                    &b.ap(
                        "elicc2",
                        &binds! {"A" => b.class("0"), "B" => b.class("_pi"),
                        "C" => b.class(&size)},
                        &[],
                    ),
                ],
            ),
        ],
    );
    let parts = binds! {"ph" => b.wff(held), "ps" => b.wff(&format!("{size} e. RR")),
    "ch" => b.wff(&format!("0 <_ {size}")), "th" => b.wff(&format!("{size} <_ _pi"))};
    out.push(Lemma::new(
        "gangbnd3",
        format!("|- ( {} -> ( {} -> {both} ) )", s.points, s.apart),
        b.ap(
            "ex",
            &binds! {"ph" => b.wff(s.points), "ps" => b.wff(s.apart),
            "ch" => b.wff(&both)},
            &[&b.ap(
                "jca",
                &binds! {"ph" => b.wff(held), "ps" => b.wff(&format!("{size} e. RR")),
                "ch" => b.wff(&format!("0 <_ {size}"))},
                &[
                    &b.ap("simp1d", &parts, &[&spelt]),
                    &b.ap("simp2d", &parts, &[&spelt]),
                ],
            )],
        ),
    ));
}

/// set.mm's law of cosines, said the way this corpus says things.
///
/// `lawcos` takes the angle function as a hypothesis, and the function it
/// takes is `df-ang` to the token, which is why the corpus declares that
/// constant and not another. Two things still have to move: `lawcos` names
/// the third side |C − B| where the corpus names it |B − C|, and it uses the
/// signed angle where the corpus uses the unsigned one. `abssub` and
/// `gcosabs` are those two steps.
fn law_of_cosines(b: &mut Builder, out: &mut Vec<Lemma>) {
    let points = "( A e. CC /\\ B e. CC /\\ C e. CC )";
    let apart = "( -. A = B /\\ -. C = B )";
    let ph = format!("( {points} /\\ {apart} )");
    let (ab, cb, bc, ca) = ("( A - B )", "( C - B )", "( B - C )", "( C - A )");
    let signed = format!("( {ab} ang {cb} )");
    let says = format!(
        "|- ( {ph} -> ( ( abs ` {ca} ) ^ 2 ) = ( ( ( ( abs ` {ab} ) ^ 2 ) + ( ( abs ` {bc} ) ^ 2 ) ) - ( 2 x. ( ( ( abs ` {ab} ) x. ( abs ` {bc} ) ) x. ( cos ` ( abs ` {signed} ) ) ) ) ) )"
    );
    {
        let b: &Builder = b;
        let mem = members(b, points, apart);
        let two = binds! {"ph" => b.wff("-. A = B"), "ps" => b.wff("-. C = B")};
        let mut unequal: IndexMap<&str, Proof> = IndexMap::new();
        for (name, pick, claim) in
            [("AB", "simpl", "-. A = B"), ("CB", "simpr", "-. C = B")]
        {
            unequal.insert(
                name,
                b.ap(
                    "adantl",
                    &binds! {"ph" => b.wff(apart),
                    "ps" => b.wff(claim),
                    "ch" => b.wff(points)},
                    &[&b.ap(pick, &two, &[])],
                ),
            );
        }

        // lawcos asks for the two disequalities the other way round, and as
        // =/= rather than as a negated equation.
        let ne = |x: &str, y: &str, which: &str| -> Proof {
            b.ap(
                "neqned",
                &binds! {"ph" => b.wff(&ph), "A" => b.class(x), "B" => b.class(y)},
                &[&unequal[which]],
            )
        };

        let raw = b.ap(
            "syl2anc",
            &binds! {"ph" => b.wff(&ph),
            "ps" => b.wff("( C e. CC /\\ A e. CC /\\ B e. CC )"),
            "ch" => b.wff("( C =/= B /\\ A =/= B )"),
            "th" => b.wff(&format!("( ( abs ` {ca} ) ^ 2 ) = ( ( ( ( abs ` {ab} ) ^ 2 ) + ( ( abs ` {cb} ) ^ 2 ) ) - ( 2 x. ( ( ( abs ` {ab} ) x. ( abs ` {cb} ) ) x. ( cos ` {signed} ) ) ) )"))},
            &[
                &b.ap(
                    "3jca",
                    &binds! {"ph" => b.wff(&ph), "ps" => b.wff("C e. CC"),
                    "ch" => b.wff("A e. CC"), "th" => b.wff("B e. CC")},
                    &[&mem["C"], &mem["A"], &mem["B"]],
                ),
                &b.ap(
                    "jca",
                    &binds! {"ph" => b.wff(&ph), "ps" => b.wff("C =/= B"),
                    "ch" => b.wff("A =/= B")},
                    &[&ne("C", "B", "CB"), &ne("A", "B", "AB")],
                ),
                &b.ap(
                    "lawcos",
                    &binds! {"A" => b.class("C"), "B" => b.class("A"), "C" => b.class("B"),
                    "F" => b.class("ang"), "O" => b.class(&signed),
                    "X" => b.class(&format!("( abs ` {ab} )")),
                    "Y" => b.class(&format!("( abs ` {cb} )")),
                    "Z" => b.class(&format!("( abs ` {ca} )"))},
                    &[
                        &b.ap("df-ang", &binds! {}, &[]),
                        &b.ap("eqid", &binds! {"A" => b.class(&format!("( abs ` {ab} )"))}, &[]),
                        &b.ap("eqid", &binds! {"A" => b.class(&format!("( abs ` {cb} )"))}, &[]),
                        &b.ap("eqid", &binds! {"A" => b.class(&format!("( abs ` {ca} )"))}, &[]),
                        &b.ap("eqid", &binds! {"A" => b.class(&signed)}, &[]),
                    ],
                ),
            ],
        );

        // |C - B| is |B - C|, and the cosine does not see the angle's sign.
        let flip = b.ap(
            "syl2anc",
            &binds! {"ph" => b.wff(&ph), "ps" => b.wff("C e. CC"),
            "ch" => b.wff("B e. CC"),
            "th" => b.wff(&format!("( abs ` {cb} ) = ( abs ` {bc} )"))},
            &[
                &mem["C"],
                &mem["B"],
                &b.ap(
                    "abssub",
                    &binds! {"A" => b.class("C"), "B" => b.class("B")},
                    &[],
                ),
            ],
        );
        let ab_cc = b.ap(
            "subcld",
            &binds! {"ph" => b.wff(&ph), "A" => b.class("A"), "B" => b.class("B")},
            &[&mem["A"], &mem["B"]],
        );
        let cb_cc = b.ap(
            "subcld",
            &binds! {"ph" => b.wff(&ph), "A" => b.class("C"), "B" => b.class("B")},
            &[&mem["C"], &mem["B"]],
        );
        let ab_nz = differs(b, &ph, "A", "B", &mem["A"], &mem["B"], &unequal["AB"]);
        let cb_nz = differs(b, &ph, "C", "B", &mem["C"], &mem["B"], &unequal["CB"]);
        let quotient = b.ap(
            "divcld",
            &binds! {"ph" => b.wff(&ph), "A" => b.class(cb),
            "B" => b.class(ab)},
            &[&cb_cc, &ab_cc, &ab_nz],
        );
        let ready = b.ap(
            "jca",
            &binds! {"ph" => b.wff(&ph),
            "ps" => b.wff(&format!("( {ab} e. CC /\\ {ab} =/= 0 )")),
            "ch" => b.wff(&format!("( {cb} e. CC /\\ {cb} =/= 0 )"))},
            &[
                &b.ap(
                    "jca",
                    &binds! {"ph" => b.wff(&ph), "ps" => b.wff(&format!("{ab} e. CC")),
                    "ch" => b.wff(&format!("{ab} =/= 0"))},
                    &[&ab_cc, &ab_nz],
                ),
                &b.ap(
                    "jca",
                    &binds! {"ph" => b.wff(&ph), "ps" => b.wff(&format!("{cb} e. CC")),
                    "ch" => b.wff(&format!("{cb} =/= 0"))},
                    &[&cb_cc, &cb_nz],
                ),
            ],
        );
        let ang_value = b.ap(
            "syl",
            &binds! {"ph" => b.wff(&ph),
            "ps" => b.wff(&format!("( ( {ab} e. CC /\\ {ab} =/= 0 ) /\\ ( {cb} e. CC /\\ {cb} =/= 0 ) )")),
            "ch" => b.wff(&format!("{signed} = ( Im ` ( log ` ( {cb} / {ab} ) ) )"))},
            &[
                &ready,
                &b.ap("gangval", &binds! {"A" => b.class(ab), "B" => b.class(cb)}, &[]),
            ],
        );
        let signed_re = b.ap(
            "eqeltrd",
            &binds! {"ph" => b.wff(&ph), "A" => b.class(&signed),
            "B" => b.class(&format!("( Im ` ( log ` ( {cb} / {ab} ) ) )")),
            "C" => b.class("RR")},
            &[
                &ang_value,
                &b.ap(
                    "imcld",
                    &binds! {"ph" => b.wff(&ph),
                    "A" => b.class(&format!("( log ` ( {cb} / {ab} ) )"))},
                    &[&b.ap(
                        "logcld",
                        &binds! {"ph" => b.wff(&ph),
                        "X" => b.class(&format!("( {cb} / {ab} )"))},
                        &[
                            &quotient,
                            &b.ap(
                                "divne0d",
                                &binds! {"ph" => b.wff(&ph), "A" => b.class(cb),
                                "B" => b.class(ab)},
                                &[&cb_cc, &ab_cc, &cb_nz, &ab_nz],
                            ),
                        ],
                    )],
                ),
            ],
        );
        let unsign = b.ap(
            "eqcomd",
            &binds! {"ph" => b.wff(&ph),
            "A" => b.class(&format!("( cos ` ( abs ` {signed} ) )")),
            "B" => b.class(&format!("( cos ` {signed} )"))},
            &[&b.ap(
                "syl",
                &binds! {"ph" => b.wff(&ph), "ps" => b.wff(&format!("{signed} e. RR")),
                "ch" => b.wff(&format!("( cos ` ( abs ` {signed} ) ) = ( cos ` {signed} )"))},
                &[
                    &signed_re,
                    &b.ap("gcosabs", &binds! {"A" => b.class(&signed)}, &[]),
                ],
            )],
        );
        let proof = b.ap(
            "eqtrd",
            &binds! {"ph" => b.wff(&ph), "A" => b.class(&format!("( ( abs ` {ca} ) ^ 2 )")),
            "B" => b.class(&format!("( ( ( ( abs ` {ab} ) ^ 2 ) + ( ( abs ` {cb} ) ^ 2 ) ) - ( 2 x. ( ( ( abs ` {ab} ) x. ( abs ` {cb} ) ) x. ( cos ` {signed} ) ) ) )")),
            "C" => b.class(&format!("( ( ( ( abs ` {ab} ) ^ 2 ) + ( ( abs ` {bc} ) ^ 2 ) ) - ( 2 x. ( ( ( abs ` {ab} ) x. ( abs ` {bc} ) ) x. ( cos ` ( abs ` {signed} ) ) ) ) )"))},
            &[
                &raw,
                &b.ap(
                    "oveq12d",
                    &binds! {"ph" => b.wff(&ph),
                    "A" => b.class(&format!("( ( ( abs ` {ab} ) ^ 2 ) + ( ( abs ` {cb} ) ^ 2 ) )")),
                    "B" => b.class(&format!("( ( ( abs ` {ab} ) ^ 2 ) + ( ( abs ` {bc} ) ^ 2 ) )")),
                    "C" => b.class(&format!("( 2 x. ( ( ( abs ` {ab} ) x. ( abs ` {cb} ) ) x. ( cos ` {signed} ) ) )")),
                    "D" => b.class(&format!("( 2 x. ( ( ( abs ` {ab} ) x. ( abs ` {bc} ) ) x. ( cos ` ( abs ` {signed} ) ) ) )")),
                    "F" => b.class("-")},
                    &[
                        &b.ap(
                            "oveq2d",
                            &binds! {"ph" => b.wff(&ph),
                            "A" => b.class(&format!("( ( abs ` {cb} ) ^ 2 )")),
                            "B" => b.class(&format!("( ( abs ` {bc} ) ^ 2 )")),
                            "C" => b.class(&format!("( ( abs ` {ab} ) ^ 2 )")),
                            "F" => b.class("+")},
                            &[&b.ap(
                                "oveq1d",
                                &binds! {"ph" => b.wff(&ph),
                                "A" => b.class(&format!("( abs ` {cb} )")),
                                "B" => b.class(&format!("( abs ` {bc} )")),
                                "C" => b.class("2"), "F" => b.class("^")},
                                &[&flip],
                            )],
                        ),
                        &b.ap(
                            "oveq2d",
                            &binds! {"ph" => b.wff(&ph),
                            "A" => b.class(&format!("( ( ( abs ` {ab} ) x. ( abs ` {cb} ) ) x. ( cos ` {signed} ) )")),
                            "B" => b.class(&format!("( ( ( abs ` {ab} ) x. ( abs ` {bc} ) ) x. ( cos ` ( abs ` {signed} ) ) )")),
                            "C" => b.class("2"), "F" => b.class("x.")},
                            &[&b.ap(
                                "oveq12d",
                                &binds! {"ph" => b.wff(&ph),
                                "A" => b.class(&format!("( ( abs ` {ab} ) x. ( abs ` {cb} ) )")),
                                "B" => b.class(&format!("( ( abs ` {ab} ) x. ( abs ` {bc} ) )")),
                                "C" => b.class(&format!("( cos ` {signed} )")),
                                "D" => b.class(&format!("( cos ` ( abs ` {signed} ) )")),
                                "F" => b.class("x.")},
                                &[
                                    &b.ap(
                                        "oveq2d",
                                        &binds! {"ph" => b.wff(&ph),
                                        "A" => b.class(&format!("( abs ` {cb} )")),
                                        "B" => b.class(&format!("( abs ` {bc} )")),
                                        "C" => b.class(&format!("( abs ` {ab} )")),
                                        "F" => b.class("x.")},
                                        &[&flip],
                                    ),
                                    &unsign,
                                ],
                            )],
                        ),
                    ],
                ),
            ],
        );
        out.push(Lemma::new("glawcos", says.clone(), proof));
    }
    b.define("glawcos", &says);
}

/// Two laws of cosines with the same sides say the same cosine.
///
/// Both sides of the comparison have the shape Z − 2(K·X), where Z is the
/// two squares added and K the two sides multiplied. What is wanted is X, so
/// Z comes off by `subcan` and the two factors by `mulcan`. K is a product of
/// two lengths and is nonzero because neither vertex meets the one the angle
/// sits at.
fn cancelling(b: &mut Builder, out: &mut Vec<Lemma>) {
    let ph = "( ( X e. CC /\\ Y e. CC /\\ Z e. CC ) /\\ ( K e. CC /\\ K =/= 0 ) )";
    let (left, right) = ("( 2 x. ( K x. X ) )", "( 2 x. ( K x. Y ) )");
    let says = format!("|- ( {ph} -> ( ( Z - {left} ) = ( Z - {right} ) -> X = Y ) )");
    {
        let b: &Builder = b;
        let three = b.ap(
            "simpl",
            &binds! {"ph" => b.wff("( X e. CC /\\ Y e. CC /\\ Z e. CC )"),
            "ps" => b.wff("( K e. CC /\\ K =/= 0 )")},
            &[],
        );
        let mut mem: IndexMap<&str, Proof> = IndexMap::new();
        for (name, which) in [("X", "simp1"), ("Y", "simp2"), ("Z", "simp3")] {
            mem.insert(
                name,
                b.ap(
                    "syl",
                    &binds! {"ph" => b.wff(ph),
                    "ps" => b.wff("( X e. CC /\\ Y e. CC /\\ Z e. CC )"),
                    "ch" => b.wff(&format!("{name} e. CC"))},
                    &[
                        &three,
                        &b.ap(
                            which,
                            &binds! {"ph" => b.wff("X e. CC"),
                            "ps" => b.wff("Y e. CC"),
                            "ch" => b.wff("Z e. CC")},
                            &[],
                        ),
                    ],
                ),
            );
        }
        let pair = b.ap(
            "simpr",
            &binds! {"ph" => b.wff("( X e. CC /\\ Y e. CC /\\ Z e. CC )"),
            "ps" => b.wff("( K e. CC /\\ K =/= 0 )")},
            &[],
        );
        let k_cc = b.ap(
            "simpld",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff("K e. CC"),
            "ch" => b.wff("K =/= 0")},
            &[&pair],
        );
        let two = b.ap(
            "a1i",
            &binds! {"ph" => b.wff("2 e. CC"), "ps" => b.wff(ph)},
            &[&b.step("2cn")],
        );
        let two_nz = b.ap(
            "a1i",
            &binds! {"ph" => b.wff("2 =/= 0"), "ps" => b.wff(ph)},
            &[&b.step("2ne0")],
        );
        let k_times = |v: &str| -> Proof {
            b.ap(
                "mulcld",
                &binds! {"ph" => b.wff(ph), "A" => b.class("K"),
                "B" => b.class(v)},
                &[&k_cc, &mem[v]],
            )
        };

        // Z comes off first, then the 2, then K.
        let drops_z = b.ap(
            "syl3anc",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff("Z e. CC"),
            "ch" => b.wff(&format!("{left} e. CC")), "th" => b.wff(&format!("{right} e. CC")),
            "ta" => b.wff(&format!("( ( Z - {left} ) = ( Z - {right} ) <-> {left} = {right} )"))},
            &[
                &mem["Z"],
                &b.ap(
                    "mulcld",
                    &binds! {"ph" => b.wff(ph), "A" => b.class("2"),
                    "B" => b.class("( K x. X )")},
                    &[&two, &k_times("X")],
                ),
                &b.ap(
                    "mulcld",
                    &binds! {"ph" => b.wff(ph), "A" => b.class("2"),
                    "B" => b.class("( K x. Y )")},
                    &[&two, &k_times("Y")],
                ),
                &b.ap(
                    "subcan",
                    &binds! {"A" => b.class("Z"), "B" => b.class(left),
                    "C" => b.class(right)},
                    &[],
                ),
            ],
        );
        let drops_two = b.ap(
            "syl3anc",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff("( K x. X ) e. CC"),
            "ch" => b.wff("( K x. Y ) e. CC"),
            "th" => b.wff("( 2 e. CC /\\ 2 =/= 0 )"),
            "ta" => b.wff(&format!("( {left} = {right} <-> ( K x. X ) = ( K x. Y ) )"))},
            &[
                &k_times("X"),
                &k_times("Y"),
                &b.ap(
                    "jca",
                    &binds! {"ph" => b.wff(ph), "ps" => b.wff("2 e. CC"),
                    "ch" => b.wff("2 =/= 0")},
                    &[&two, &two_nz],
                ),
                &b.ap(
                    "mulcan",
                    &binds! {"A" => b.class("( K x. X )"),
                    "B" => b.class("( K x. Y )"),
                    "C" => b.class("2")},
                    &[],
                ),
            ],
        );
        let drops_k = b.ap(
            "syl3anc",
            &binds! {"ph" => b.wff(ph), "ps" => b.wff("X e. CC"),
            "ch" => b.wff("Y e. CC"),
            "th" => b.wff("( K e. CC /\\ K =/= 0 )"),
            "ta" => b.wff("( ( K x. X ) = ( K x. Y ) <-> X = Y )")},
            &[
                &mem["X"],
                &mem["Y"],
                &pair,
                &b.ap(
                    "mulcan",
                    &binds! {"A" => b.class("X"), "B" => b.class("Y"),
                    "C" => b.class("K")},
                    &[],
                ),
            ],
        );
        let proof = b.ap(
            "sylibd",
            &binds! {"ph" => b.wff(ph),
            "ps" => b.wff(&format!("( Z - {left} ) = ( Z - {right} )")),
            "ch" => b.wff("( K x. X ) = ( K x. Y )"),
            "th" => b.wff("X = Y")},
            &[
                &b.ap(
                    "sylibd",
                    &binds! {"ph" => b.wff(ph),
                    "ps" => b.wff(&format!("( Z - {left} ) = ( Z - {right} )")),
                    "ch" => b.wff(&format!("{left} = {right}")),
                    "th" => b.wff("( K x. X ) = ( K x. Y )")},
                    &[
                        &b.ap(
                            "biimpd",
                            &binds! {"ph" => b.wff(ph),
                            "ps" => b.wff(&format!("( Z - {left} ) = ( Z - {right} )")),
                            "ch" => b.wff(&format!("{left} = {right}"))},
                            &[&drops_z],
                        ),
                        &drops_two,
                    ],
                ),
                &drops_k,
            ],
        );
        out.push(Lemma::new("gcoscan", says.clone(), proof));
    }
    b.define("gcoscan", &says);

    // Going back from the cosine to the angle, which is possible only
    // because the angle the corpus writes is unsigned: cosine is one to one
    // on 0 to pi and on nothing wider.
    let nz = "( ( A e. CC /\\ A =/= 0 ) /\\ ( B e. CC /\\ B =/= 0 ) )";
    let nz2 = "( ( C e. CC /\\ C =/= 0 ) /\\ ( D e. CC /\\ D =/= 0 ) )";
    let both = format!("( {nz} /\\ {nz2} )");
    let (one, two) = ("( abs ` ( A ang B ) )", "( abs ` ( C ang D ) )");
    let says = format!(
        "|- ( {both} -> ( ( cos ` {one} ) = ( cos ` {two} ) -> {one} = {two} ) )"
    );
    {
        let b: &Builder = b;
        let proof = b.ap(
            "biimprd",
            &binds! {"ph" => b.wff(&both), "ps" => b.wff(&format!("{one} = {two}")),
            "ch" => b.wff(&format!("( cos ` {one} ) = ( cos ` {two} )"))},
            &[&b.ap(
                "syl2anc",
                &binds! {"ph" => b.wff(&both), "ps" => b.wff(&format!("{one} e. ( 0 [,] _pi )")),
                "ch" => b.wff(&format!("{two} e. ( 0 [,] _pi )")),
                "th" => b.wff(&format!("( {one} = {two} <-> ( cos ` {one} ) = ( cos ` {two} ) )"))},
                &[
                    &b.ap(
                        "syl",
                        &binds! {"ph" => b.wff(&both), "ps" => b.wff(nz),
                        "ch" => b.wff(&format!("{one} e. ( 0 [,] _pi )"))},
                        &[
                            &b.ap(
                                "simpl",
                                &binds! {"ph" => b.wff(nz), "ps" => b.wff(nz2)},
                                &[],
                            ),
                            &b.ap(
                                "gangrange",
                                &binds! {"A" => b.class("A"), "B" => b.class("B")},
                                &[],
                            ),
                        ],
                    ),
                    &b.ap(
                        "syl",
                        &binds! {"ph" => b.wff(&both), "ps" => b.wff(nz2),
                        "ch" => b.wff(&format!("{two} e. ( 0 [,] _pi )"))},
                        &[
                            &b.ap(
                                "simpr",
                                &binds! {"ph" => b.wff(nz), "ps" => b.wff(nz2)},
                                &[],
                            ),
                            &b.ap(
                                "gangrange",
                                &binds! {"A" => b.class("C"), "B" => b.class("D")},
                                &[],
                            ),
                        ],
                    ),
                    &b.ap("cos11", &binds! {"A" => b.class(one), "B" => b.class(two)}, &[]),
                ],
            )],
        );
        out.push(Lemma::new("gangeq", says.clone(), proof));
    }
    b.define("gangeq", &says);
}

fn side(x: &str, y: &str) -> String {
    format!("( abs ` ( {x} - {y} ) )")
}

/// The corpus's unsigned angle at y, between the rays to x and z.
fn at(x: &str, y: &str, z: &str) -> String {
    format!("( abs ` ( ( {x} - {y} ) ang ( {z} - {y} ) ) )")
}

/// The disequalities between two of three points, by the pair.
type Apart = IndexMap<(String, String), Proof>;

/// Two sides and the angle between them fix the triangle.
///
/// An axiom in Euclid and in Hilbert, because a synthetic geometry has no
/// coordinates to compute with and congruence has to be stipulated. Over CC
/// it is a theorem, and this is the proof: the law of cosines at each of the
/// three vertices, six applications in all, which are three cyclic rotations
/// of `glawcos` in each triangle.
///
/// The third side comes first, from the law at the given angle's vertex,
/// since equal sides and equal cosines make equal squares and a length is
/// not negative. With all three sides equal the other two angles follow the
/// other way round: the law at each of the remaining vertices has the same
/// sides on both sides of the comparison, so `gcoscan` leaves the cosines
/// equal and `gangeq` turns that back into the angles.
fn side_angle_side(b: &mut Builder, out: &mut Vec<Lemma>) {
    let first = "( P e. CC /\\ Q e. CC /\\ R e. CC )";
    let second = "( S e. CC /\\ T e. CC /\\ U e. CC )";
    let pts = format!("( {first} /\\ {second} )");
    let (tri1, tri2) = (triangle("P", "Q", "R"), triangle("S", "T", "U"));

    let same_pq = format!("{} = {}", side("P", "Q"), side("S", "T"));
    let same_qr = format!("{} = {}", side("Q", "R"), side("T", "U"));
    let same_rp = format!("{} = {}", side("R", "P"), side("U", "S"));
    let ang_q = format!("{} = {}", at("P", "Q", "R"), at("S", "T", "U"));
    let ang_r = format!("{} = {}", at("Q", "R", "P"), at("T", "U", "S"));
    let ang_p = format!("{} = {}", at("R", "P", "Q"), at("U", "S", "T"));

    // The antecedents nest to the left, so a fact proved under a prefix is
    // carried out to the whole by one `adantr` for each later one.
    let levels: Vec<String> = vec![
        pts.clone(),
        tri1.clone(),
        tri2.clone(),
        same_pq.clone(),
        ang_q.clone(),
        same_qr.clone(),
    ];
    let mut ws: Vec<String> = vec![levels[0].clone()];
    for one in &levels[1..] {
        let next = format!("( {} /\\ {one} )", ws[ws.len() - 1]);
        ws.push(next);
    }
    let whole = ws[ws.len() - 1].clone();
    let (proof, says) = {
        let b: &Builder = b;
        let lift = |claim: &str, proof: Proof, frm: usize| -> Proof {
            let mut proof = proof;
            for i in frm..levels.len() - 1 {
                proof = b.ap(
                    "adantr",
                    &binds! {"ph" => b.wff(&ws[i]), "ps" => b.wff(claim),
                    "ch" => b.wff(&levels[i + 1])},
                    &[&proof],
                );
            }
            proof
        };

        // The i-th antecedent, as a fact of the whole.
        let given = |i: usize| -> Proof {
            lift(
                &levels[i],
                b.ap(
                    "simpr",
                    &binds! {"ph" => b.wff(&ws[i - 1]),
                    "ps" => b.wff(&levels[i])},
                    &[],
                ),
                i,
            )
        };

        let mut mem: IndexMap<&str, Proof> = IndexMap::new();
        for (name, which, half) in [
            ("P", "simp1", "simpl"),
            ("Q", "simp2", "simpl"),
            ("R", "simp3", "simpl"),
            ("S", "simp1", "simpr"),
            ("T", "simp2", "simpr"),
            ("U", "simp3", "simpr"),
        ] {
            let side_of = if half == "simpl" { first } else { second };
            let names = if half == "simpl" {
                ["P", "Q", "R"]
            } else {
                ["S", "T", "U"]
            };
            mem.insert(
                name,
                lift(
                    &format!("{name} e. CC"),
                    b.ap(
                        "syl",
                        &binds! {"ph" => b.wff(&pts), "ps" => b.wff(side_of),
                        "ch" => b.wff(&format!("{name} e. CC"))},
                        &[
                            &b.ap(
                                half,
                                &binds! {"ph" => b.wff(first), "ps" => b.wff(second)},
                                &[],
                            ),
                            &b.ap(
                                which,
                                &binds! {"ph" => b.wff(&format!("{} e. CC", names[0])),
                                "ps" => b.wff(&format!("{} e. CC", names[1])),
                                "ch" => b.wff(&format!("{} e. CC", names[2]))},
                                &[],
                            ),
                        ],
                    ),
                    0,
                ),
            );
        }

        // The three disequalities a triangle states, as facts of the whole.
        //
        // The predicate is ((( x!=y & y!=z ) & x!=z ) & not collinear), so
        // the three come off by taking the left conjunct twice and then the
        // halves; the reversed ones the rotations want come off `flipped`.
        let apart_of = |x: &str, y: &str, z: &str, level: usize| -> Apart {
            let inner =
                format!("( ( -. {x} = {y} /\\ -. {y} = {z} ) /\\ -. {x} = {z} )");
            let pair = format!("( -. {x} = {y} /\\ -. {y} = {z} )");
            let held = given(level);
            let cut = b.ap(
                "simpld",
                &binds! {"ph" => b.wff(&whole), "ps" => b.wff(&inner),
                "ch" => b.wff(&format!("-. ( ( {z} - {x} ) / ( {y} - {x} ) ) e. RR"))},
                &[&held],
            );
            let two = b.ap(
                "simpld",
                &binds! {"ph" => b.wff(&whole), "ps" => b.wff(&pair),
                "ch" => b.wff(&format!("-. {x} = {z}"))},
                &[&cut],
            );
            let mut out: Apart = IndexMap::new();
            out.insert(
                (x.to_string(), z.to_string()),
                b.ap(
                    "simprd",
                    &binds! {"ph" => b.wff(&whole), "ps" => b.wff(&pair),
                    "ch" => b.wff(&format!("-. {x} = {z}"))},
                    &[&cut],
                ),
            );
            out.insert(
                (x.to_string(), y.to_string()),
                b.ap(
                    "simpld",
                    &binds! {"ph" => b.wff(&whole),
                    "ps" => b.wff(&format!("-. {x} = {y}")),
                    "ch" => b.wff(&format!("-. {y} = {z}"))},
                    &[&two],
                ),
            );
            out.insert(
                (y.to_string(), z.to_string()),
                b.ap(
                    "simprd",
                    &binds! {"ph" => b.wff(&whole),
                    "ps" => b.wff(&format!("-. {x} = {y}")),
                    "ch" => b.wff(&format!("-. {y} = {z}"))},
                    &[&two],
                ),
            );
            let listed: Vec<((String, String), Proof)> =
                out.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
            for ((a, c), proof) in listed {
                out.insert((c.clone(), a.clone()), flipped(b, &whole, &a, &c, &proof));
            }
            out
        };

        let ne1 = apart_of("P", "Q", "R", 1);
        let ne2 = apart_of("S", "T", "U", 2);
        let key = |x: &str, y: &str| (x.to_string(), y.to_string());

        // `glawcos` at y: the side opposite y from the two sides at it.
        let law = |x: &str, y: &str, z: &str, ne: &Apart| -> Proof {
            b.ap(
                "syl",
                &binds! {"ph" => b.wff(&whole),
                "ps" => b.wff(&format!("( ( {x} e. CC /\\ {y} e. CC /\\ {z} e. CC ) /\\ ( -. {x} = {y} /\\ -. {z} = {y} ) )")),
                "ch" => b.wff(&format!(
                    "( {} ^ 2 ) = ( ( ( {} ^ 2 ) + ( {} ^ 2 ) ) - ( 2 x. ( ( {} x. {} ) x. ( cos ` {} ) ) ) )",
                    side(z, x), side(x, y), side(y, z), side(x, y), side(y, z), at(x, y, z)
                ))},
                &[
                    &b.ap(
                        "jca",
                        &binds! {"ph" => b.wff(&whole),
                        "ps" => b.wff(&format!("( {x} e. CC /\\ {y} e. CC /\\ {z} e. CC )")),
                        "ch" => b.wff(&format!("( -. {x} = {y} /\\ -. {z} = {y} )"))},
                        &[
                            &b.ap(
                                "3jca",
                                &binds! {"ph" => b.wff(&whole), "ps" => b.wff(&format!("{x} e. CC")),
                                "ch" => b.wff(&format!("{y} e. CC")),
                                "th" => b.wff(&format!("{z} e. CC"))},
                                &[&mem[x], &mem[y], &mem[z]],
                            ),
                            &b.ap(
                                "jca",
                                &binds! {"ph" => b.wff(&whole),
                                "ps" => b.wff(&format!("-. {x} = {y}")),
                                "ch" => b.wff(&format!("-. {z} = {y}"))},
                                &[&ne[&key(x, y)], &ne[&key(z, y)]],
                            ),
                        ],
                    ),
                    &b.ap(
                        "glawcos",
                        &binds! {"A" => b.class(x), "B" => b.class(y), "C" => b.class(z)},
                        &[],
                    ),
                ],
            )
        };

        // The two right-hand sides agree, component by component.
        #[allow(clippy::too_many_arguments)]
        let right_hand = |a1: &str,
                          a2: &str,
                          b1: &str,
                          b2: &str,
                          x1: &str,
                          x2: &str,
                          ea: &Proof,
                          eb: &Proof,
                          ex_: &Proof|
         -> Proof {
            let squares = b.ap(
                "oveq12d",
                &binds! {"ph" => b.wff(&whole), "A" => b.class(&format!("( {a1} ^ 2 )")),
                "B" => b.class(&format!("( {a2} ^ 2 )")),
                "C" => b.class(&format!("( {b1} ^ 2 )")),
                "D" => b.class(&format!("( {b2} ^ 2 )")), "F" => b.class("+")},
                &[
                    &b.ap(
                        "oveq1d",
                        &binds! {"ph" => b.wff(&whole), "A" => b.class(a1), "B" => b.class(a2),
                        "C" => b.class("2"), "F" => b.class("^")},
                        &[ea],
                    ),
                    &b.ap(
                        "oveq1d",
                        &binds! {"ph" => b.wff(&whole), "A" => b.class(b1), "B" => b.class(b2),
                        "C" => b.class("2"), "F" => b.class("^")},
                        &[eb],
                    ),
                ],
            );
            let product = b.ap(
                "oveq12d",
                &binds! {"ph" => b.wff(&whole), "A" => b.class(&format!("( {a1} x. {b1} )")),
                "B" => b.class(&format!("( {a2} x. {b2} )")), "C" => b.class(x1),
                "D" => b.class(x2), "F" => b.class("x.")},
                &[
                    &b.ap(
                        "oveq12d",
                        &binds! {"ph" => b.wff(&whole), "A" => b.class(a1),
                        "B" => b.class(a2), "C" => b.class(b1), "D" => b.class(b2),
                        "F" => b.class("x.")},
                        &[ea, eb],
                    ),
                    ex_,
                ],
            );
            b.ap(
                "oveq12d",
                &binds! {"ph" => b.wff(&whole),
                "A" => b.class(&format!("( ( {a1} ^ 2 ) + ( {b1} ^ 2 ) )")),
                "B" => b.class(&format!("( ( {a2} ^ 2 ) + ( {b2} ^ 2 ) )")),
                "C" => b.class(&format!("( 2 x. ( ( {a1} x. {b1} ) x. {x1} ) )")),
                "D" => b.class(&format!("( 2 x. ( ( {a2} x. {b2} ) x. {x2} ) )")),
                "F" => b.class("-")},
                &[
                    &squares,
                    &b.ap(
                        "oveq2d",
                        &binds! {"ph" => b.wff(&whole),
                        "A" => b.class(&format!("( ( {a1} x. {b1} ) x. {x1} )")),
                        "B" => b.class(&format!("( ( {a2} x. {b2} ) x. {x2} )")),
                        "C" => b.class("2"), "F" => b.class("x.")},
                        &[&product],
                    ),
                ],
            )
        };

        // An equality of angles, read through cosine.
        let cosines = |equal: &Proof, one: &str, two: &str| -> Proof {
            b.ap(
                "fveq2d",
                &binds! {"ph" => b.wff(&whole), "A" => b.class(one),
                "B" => b.class(two), "F" => b.class("cos")},
                &[equal],
            )
        };

        let difference = |x: &str, y: &str| -> Proof {
            b.ap(
                "subcld",
                &binds! {"ph" => b.wff(&whole), "A" => b.class(x),
                "B" => b.class(y)},
                &[&mem[x], &mem[y]],
            )
        };

        // The third side. Equal sides and an equal angle make equal squares,
        // and a length is not negative, so the sides themselves are equal.
        let squares_rp = b.ap(
            "3eqtr4d",
            &binds! {"ph" => b.wff(&whole),
            "A" => b.class(&format!(
                "( ( ( {} ^ 2 ) + ( {} ^ 2 ) ) - ( 2 x. ( ( {} x. {} ) x. ( cos ` {} ) ) ) )",
                side("P", "Q"), side("Q", "R"), side("P", "Q"), side("Q", "R"), at("P", "Q", "R")
            )),
            "B" => b.class(&format!(
                "( ( ( {} ^ 2 ) + ( {} ^ 2 ) ) - ( 2 x. ( ( {} x. {} ) x. ( cos ` {} ) ) ) )",
                side("S", "T"), side("T", "U"), side("S", "T"), side("T", "U"), at("S", "T", "U")
            )),
            "C" => b.class(&format!("( {} ^ 2 )", side("R", "P"))),
            "D" => b.class(&format!("( {} ^ 2 )", side("U", "S")))},
            &[
                &right_hand(
                    &side("P", "Q"),
                    &side("S", "T"),
                    &side("Q", "R"),
                    &side("T", "U"),
                    &format!("( cos ` {} )", at("P", "Q", "R")),
                    &format!("( cos ` {} )", at("S", "T", "U")),
                    &given(3),
                    &given(5),
                    &cosines(&given(4), &at("P", "Q", "R"), &at("S", "T", "U")),
                ),
                &law("P", "Q", "R", &ne1),
                &law("S", "T", "U", &ne2),
            ],
        );
        let length = |x: &str, y: &str| -> Proof {
            b.ap(
                "jca",
                &binds! {"ph" => b.wff(&whole),
                "ps" => b.wff(&format!("{} e. RR", side(x, y))),
                "ch" => b.wff(&format!("0 <_ {}", side(x, y)))},
                &[
                    &b.ap(
                        "abscld",
                        &binds! {"ph" => b.wff(&whole),
                        "A" => b.class(&format!("( {x} - {y} )"))},
                        &[&difference(x, y)],
                    ),
                    &b.ap(
                        "absge0d",
                        &binds! {"ph" => b.wff(&whole),
                        "A" => b.class(&format!("( {x} - {y} )"))},
                        &[&difference(x, y)],
                    ),
                ],
            )
        };
        let third = b.ap(
            "mpbid",
            &binds! {"ph" => b.wff(&whole),
            "ps" => b.wff(&format!("( {} ^ 2 ) = ( {} ^ 2 )", side("R", "P"), side("U", "S"))),
            "ch" => b.wff(&same_rp)},
            &[
                &squares_rp,
                &b.ap(
                    "syl2anc",
                    &binds! {"ph" => b.wff(&whole),
                    "ps" => b.wff(&format!("( {} e. RR /\\ 0 <_ {} )", side("R", "P"), side("R", "P"))),
                    "ch" => b.wff(&format!("( {} e. RR /\\ 0 <_ {} )", side("U", "S"), side("U", "S"))),
                    "th" => b.wff(&format!("( ( {} ^ 2 ) = ( {} ^ 2 ) <-> {same_rp} )", side("R", "P"), side("U", "S")))},
                    &[
                        &length("R", "P"),
                        &length("U", "S"),
                        &b.ap(
                            "sq11",
                            &binds! {"A" => b.class(&side("R", "P")),
                            "B" => b.class(&side("U", "S"))},
                            &[],
                        ),
                    ],
                ),
            ],
        );
        let length_cc = |x: &str, y: &str| -> Proof {
            b.ap(
                "recnd",
                &binds! {"ph" => b.wff(&whole), "A" => b.class(&side(x, y))},
                &[&b.ap(
                    "abscld",
                    &binds! {"ph" => b.wff(&whole),
                    "A" => b.class(&format!("( {x} - {y} )"))},
                    &[&difference(x, y)],
                )],
            )
        };
        let length_nz = |x: &str, y: &str, ne: &Apart| -> Proof {
            b.ap(
                "absne0d",
                &binds! {"ph" => b.wff(&whole),
                "A" => b.class(&format!("( {x} - {y} )"))},
                &[
                    &difference(x, y),
                    &differs(b, &whole, x, y, &mem[x], &mem[y], &ne[&key(x, y)]),
                ],
            )
        };
        // The difference from y to a is a nonzero number.
        let apart_from = |a: &str, y: &str, ne: &Apart| -> Proof {
            b.ap(
                "jca",
                &binds! {"ph" => b.wff(&whole),
                "ps" => b.wff(&format!("( {a} - {y} ) e. CC")),
                "ch" => b.wff(&format!("( {a} - {y} ) =/= 0"))},
                &[
                    &difference(a, y),
                    &differs(b, &whole, a, y, &mem[a], &mem[y], &ne[&key(a, y)]),
                ],
            )
        };

        // The unsigned angle is a number, which `gcoscan` needs of it.
        let angle_cc = |x: &str, y: &str, z: &str, ne: &Apart| -> Proof {
            let holds = b.ap(
                "jca",
                &binds! {"ph" => b.wff(&whole),
                "ps" => b.wff(&format!("( ( {x} - {y} ) e. CC /\\ ( {x} - {y} ) =/= 0 )")),
                "ch" => b.wff(&format!("( ( {z} - {y} ) e. CC /\\ ( {z} - {y} ) =/= 0 )"))},
                &[&apart_from(x, y, ne), &apart_from(z, y, ne)],
            );
            let inside = b.ap(
                "syl",
                &binds! {"ph" => b.wff(&whole),
                "ps" => b.wff(&format!("( ( ( {x} - {y} ) e. CC /\\ ( {x} - {y} ) =/= 0 ) /\\ ( ( {z} - {y} ) e. CC /\\ ( {z} - {y} ) =/= 0 ) )")),
                "ch" => b.wff(&format!("{} e. ( 0 [,] _pi )", at(x, y, z)))},
                &[
                    &holds,
                    &b.ap(
                        "gangrange",
                        &binds! {"A" => b.class(&format!("( {x} - {y} )")),
                        "B" => b.class(&format!("( {z} - {y} )"))},
                        &[],
                    ),
                ],
            );
            let a = at(x, y, z);
            b.ap(
                "recnd",
                &binds! {"ph" => b.wff(&whole), "A" => b.class(&a)},
                &[&b.ap(
                    "simp1d",
                    &binds! {"ph" => b.wff(&whole),
                    "ps" => b.wff(&format!("{a} e. RR")),
                    "ch" => b.wff(&format!("0 <_ {a}")),
                    "th" => b.wff(&format!("{a} <_ _pi"))},
                    &[&b.ap(
                        "mpbid",
                        &binds! {"ph" => b.wff(&whole),
                        "ps" => b.wff(&format!("{a} e. ( 0 [,] _pi )")),
                        "ch" => b.wff(&format!("( {a} e. RR /\\ 0 <_ {a} /\\ {a} <_ _pi )"))},
                        &[
                            &inside,
                            &b.ap(
                                "syl2anc",
                                &binds! {"ph" => b.wff(&whole), "ps" => b.wff("0 e. RR"),
                                "ch" => b.wff("_pi e. RR"),
                                "th" => b.wff(&format!("( {a} e. ( 0 [,] _pi ) <-> ( {a} e. RR /\\ 0 <_ {a} /\\ {a} <_ _pi ) )"))},
                                &[
                                    &b.ap(
                                        "a1i",
                                        &binds! {"ph" => b.wff("0 e. RR"),
                                        "ps" => b.wff(&whole)},
                                        &[&b.step("0re")],
                                    ),
                                    &b.ap(
                                        "a1i",
                                        &binds! {"ph" => b.wff("_pi e. RR"),
                                        "ps" => b.wff(&whole)},
                                        &[&b.step("pire")],
                                    ),
                                    &b.ap(
                                        "elicc2",
                                        &binds! {"A" => b.class("0"), "B" => b.class("_pi"),
                                        "C" => b.class(&a)},
                                        &[],
                                    ),
                                ],
                            ),
                        ],
                    )],
                )],
            )
        };

        // The angle at y is the angle at y2, all three sides agreeing.
        //
        // Both laws have the same two sides at the vertex and the same side
        // opposite it, so what is left once `gcoscan` has taken the squares
        // and the factors off is the cosine, and `gangeq` is the way back.
        #[allow(clippy::too_many_arguments)]
        let angle_equal = |x: &str,
                           y: &str,
                           z: &str,
                           x2: &str,
                           y2: &str,
                           z2: &str,
                           e_opp: &Proof,
                           e_a: &Proof,
                           e_b: &Proof|
         -> Proof {
            let z_of = format!("( ( {} ^ 2 ) + ( {} ^ 2 ) )", side(x, y), side(y, z));
            let k_of = format!("( {} x. {} )", side(x, y), side(y, z));
            let (cos1, cos2) = (
                format!("( cos ` {} )", at(x, y, z)),
                format!("( cos ` {} )", at(x2, y2, z2)),
            );
            let second_side = format!(
                "( ( ( {} ^ 2 ) + ( {} ^ 2 ) ) - ( 2 x. ( ( {} x. {} ) x. {cos2} ) ) )",
                side(x2, y2),
                side(y2, z2),
                side(x2, y2),
                side(y2, z2)
            );
            // The two right-hand sides are equal because the sides opposite
            // the vertex are, and then the second is rewritten in the
            // first's own lengths so that only the cosine differs.
            let agree = b.ap(
                "3eqtr3d",
                &binds! {"ph" => b.wff(&whole), "A" => b.class(&format!("( {} ^ 2 )", side(z, x))),
                "B" => b.class(&format!("( {} ^ 2 )", side(z2, x2))),
                "C" => b.class(&format!("( {z_of} - ( 2 x. ( {k_of} x. {cos1} ) ) )")),
                "D" => b.class(&second_side)},
                &[
                    &b.ap(
                        "oveq1d",
                        &binds! {"ph" => b.wff(&whole), "A" => b.class(&side(z, x)),
                        "B" => b.class(&side(z2, x2)), "C" => b.class("2"),
                        "F" => b.class("^")},
                        &[e_opp],
                    ),
                    &law(x, y, z, &ne1),
                    &law(x2, y2, z2, &ne2),
                ],
            );
            let rewritten = right_hand(
                &side(x2, y2),
                &side(x, y),
                &side(y2, z2),
                &side(y, z),
                &cos2,
                &cos2,
                &b.ap(
                    "eqcomd",
                    &binds! {"ph" => b.wff(&whole), "A" => b.class(&side(x, y)),
                    "B" => b.class(&side(x2, y2))},
                    &[e_a],
                ),
                &b.ap(
                    "eqcomd",
                    &binds! {"ph" => b.wff(&whole), "A" => b.class(&side(y, z)),
                    "B" => b.class(&side(y2, z2))},
                    &[e_b],
                ),
                &b.ap(
                    "a1i",
                    &binds! {"ph" => b.wff(&format!("{cos2} = {cos2}")), "ps" => b.wff(&whole)},
                    &[&b.ap("eqid", &binds! {"A" => b.class(&cos2)}, &[])],
                ),
            );
            let lined = b.ap(
                "eqtrd",
                &binds! {"ph" => b.wff(&whole),
                "A" => b.class(&format!("( {z_of} - ( 2 x. ( {k_of} x. {cos1} ) ) )")),
                "B" => b.class(&second_side),
                "C" => b.class(&format!("( {z_of} - ( 2 x. ( {k_of} x. {cos2} ) ) )"))},
                &[&agree, &rewritten],
            );
            let k_cc = b.ap(
                "mulcld",
                &binds! {"ph" => b.wff(&whole), "A" => b.class(&side(x, y)),
                "B" => b.class(&side(y, z))},
                &[&length_cc(x, y), &length_cc(y, z)],
            );
            let k_nz = b.ap(
                "syl",
                &binds! {"ph" => b.wff(&whole),
                "ps" => b.wff(&format!(
                    "( ( {} e. CC /\\ {} =/= 0 ) /\\ ( {} e. CC /\\ {} =/= 0 ) )",
                    side(x, y), side(x, y), side(y, z), side(y, z)
                )),
                "ch" => b.wff(&format!("{k_of} =/= 0"))},
                &[
                    &b.ap(
                        "jca",
                        &binds! {"ph" => b.wff(&whole),
                        "ps" => b.wff(&format!("( {} e. CC /\\ {} =/= 0 )", side(x, y), side(x, y))),
                        "ch" => b.wff(&format!("( {} e. CC /\\ {} =/= 0 )", side(y, z), side(y, z)))},
                        &[
                            &b.ap(
                                "jca",
                                &binds! {"ph" => b.wff(&whole),
                                "ps" => b.wff(&format!("{} e. CC", side(x, y))),
                                "ch" => b.wff(&format!("{} =/= 0", side(x, y)))},
                                &[&length_cc(x, y), &length_nz(x, y, &ne1)],
                            ),
                            &b.ap(
                                "jca",
                                &binds! {"ph" => b.wff(&whole),
                                "ps" => b.wff(&format!("{} e. CC", side(y, z))),
                                "ch" => b.wff(&format!("{} =/= 0", side(y, z)))},
                                &[&length_cc(y, z), &length_nz(y, z, &ne1)],
                            ),
                        ],
                    ),
                    &b.ap(
                        "mulne0",
                        &binds! {"A" => b.class(&side(x, y)),
                        "B" => b.class(&side(y, z))},
                        &[],
                    ),
                ],
            );
            let equal_cos = b.ap(
                "mpd",
                &binds! {"ph" => b.wff(&whole),
                "ps" => b.wff(&format!("( {z_of} - ( 2 x. ( {k_of} x. {cos1} ) ) ) = ( {z_of} - ( 2 x. ( {k_of} x. {cos2} ) ) )")),
                "ch" => b.wff(&format!("{cos1} = {cos2}"))},
                &[
                    &lined,
                    &b.ap(
                        "syl",
                        &binds! {"ph" => b.wff(&whole),
                        "ps" => b.wff(&format!("( ( {cos1} e. CC /\\ {cos2} e. CC /\\ {z_of} e. CC ) /\\ ( {k_of} e. CC /\\ {k_of} =/= 0 ) )")),
                        "ch" => b.wff(&format!("( ( {z_of} - ( 2 x. ( {k_of} x. {cos1} ) ) ) = ( {z_of} - ( 2 x. ( {k_of} x. {cos2} ) ) ) -> {cos1} = {cos2} )"))},
                        &[
                            &b.ap(
                                "jca",
                                &binds! {"ph" => b.wff(&whole),
                                "ps" => b.wff(&format!("( {cos1} e. CC /\\ {cos2} e. CC /\\ {z_of} e. CC )")),
                                "ch" => b.wff(&format!("( {k_of} e. CC /\\ {k_of} =/= 0 )"))},
                                &[
                                    &b.ap(
                                        "3jca",
                                        &binds! {"ph" => b.wff(&whole),
                                        "ps" => b.wff(&format!("{cos1} e. CC")),
                                        "ch" => b.wff(&format!("{cos2} e. CC")),
                                        "th" => b.wff(&format!("{z_of} e. CC"))},
                                        &[
                                            &b.ap(
                                                "syl",
                                                &binds! {"ph" => b.wff(&whole),
                                                "ps" => b.wff(&format!("{} e. CC", at(x, y, z))),
                                                "ch" => b.wff(&format!("{cos1} e. CC"))},
                                                &[
                                                    &angle_cc(x, y, z, &ne1),
                                                    &b.ap("coscl", &binds! {"A" => b.class(&at(x, y, z))}, &[]),
                                                ],
                                            ),
                                            &b.ap(
                                                "syl",
                                                &binds! {"ph" => b.wff(&whole),
                                                "ps" => b.wff(&format!("{} e. CC", at(x2, y2, z2))),
                                                "ch" => b.wff(&format!("{cos2} e. CC"))},
                                                &[
                                                    &angle_cc(x2, y2, z2, &ne2),
                                                    &b.ap("coscl", &binds! {"A" => b.class(&at(x2, y2, z2))}, &[]),
                                                ],
                                            ),
                                            &b.ap(
                                                "addcld",
                                                &binds! {"ph" => b.wff(&whole),
                                                "A" => b.class(&format!("( {} ^ 2 )", side(x, y))),
                                                "B" => b.class(&format!("( {} ^ 2 )", side(y, z)))},
                                                &[
                                                    &b.ap(
                                                        "sqcld",
                                                        &binds! {"ph" => b.wff(&whole),
                                                        "A" => b.class(&side(x, y))},
                                                        &[&length_cc(x, y)],
                                                    ),
                                                    &b.ap(
                                                        "sqcld",
                                                        &binds! {"ph" => b.wff(&whole),
                                                        "A" => b.class(&side(y, z))},
                                                        &[&length_cc(y, z)],
                                                    ),
                                                ],
                                            ),
                                        ],
                                    ),
                                    &b.ap(
                                        "jca",
                                        &binds! {"ph" => b.wff(&whole),
                                        "ps" => b.wff(&format!("{k_of} e. CC")),
                                        "ch" => b.wff(&format!("{k_of} =/= 0"))},
                                        &[&k_cc, &k_nz],
                                    ),
                                ],
                            ),
                            &b.ap(
                                "gcoscan",
                                &binds! {"X" => b.class(&cos1), "Y" => b.class(&cos2),
                                "Z" => b.class(&z_of), "K" => b.class(&k_of)},
                                &[],
                            ),
                        ],
                    ),
                ],
            );
            let vertex = |a: &str, v: &str, c: &str, nn: &Apart| -> Proof {
                b.ap(
                    "jca",
                    &binds! {"ph" => b.wff(&whole),
                    "ps" => b.wff(&format!("( ( {a} - {v} ) e. CC /\\ ( {a} - {v} ) =/= 0 )")),
                    "ch" => b.wff(&format!("( ( {c} - {v} ) e. CC /\\ ( {c} - {v} ) =/= 0 )"))},
                    &[&apart_from(a, v, nn), &apart_from(c, v, nn)],
                )
            };
            let ready = b.ap(
                "jca",
                &binds! {"ph" => b.wff(&whole),
                "ps" => b.wff(&format!("( ( ( {x} - {y} ) e. CC /\\ ( {x} - {y} ) =/= 0 ) /\\ ( ( {z} - {y} ) e. CC /\\ ( {z} - {y} ) =/= 0 ) )")),
                "ch" => b.wff(&format!("( ( ( {x2} - {y2} ) e. CC /\\ ( {x2} - {y2} ) =/= 0 ) /\\ ( ( {z2} - {y2} ) e. CC /\\ ( {z2} - {y2} ) =/= 0 ) )"))},
                &[&vertex(x, y, z, &ne1), &vertex(x2, y2, z2, &ne2)],
            );
            b.ap(
                "mpd",
                &binds! {"ph" => b.wff(&whole), "ps" => b.wff(&format!("{cos1} = {cos2}")),
                "ch" => b.wff(&format!("{} = {}", at(x, y, z), at(x2, y2, z2)))},
                &[
                    &equal_cos,
                    &b.ap(
                        "syl",
                        &binds! {"ph" => b.wff(&whole),
                        "ps" => b.wff(&format!("( ( ( ( {x} - {y} ) e. CC /\\ ( {x} - {y} ) =/= 0 ) /\\ ( ( {z} - {y} ) e. CC /\\ ( {z} - {y} ) =/= 0 ) ) /\\ ( ( ( {x2} - {y2} ) e. CC /\\ ( {x2} - {y2} ) =/= 0 ) /\\ ( ( {z2} - {y2} ) e. CC /\\ ( {z2} - {y2} ) =/= 0 ) ) )")),
                        "ch" => b.wff(&format!("( {cos1} = {cos2} -> {} = {} )", at(x, y, z), at(x2, y2, z2)))},
                        &[
                            &ready,
                            &b.ap(
                                "gangeq",
                                &binds! {"A" => b.class(&format!("( {x} - {y} )")),
                                "B" => b.class(&format!("( {z} - {y} )")),
                                "C" => b.class(&format!("( {x2} - {y2} )")),
                                "D" => b.class(&format!("( {z2} - {y2} )"))},
                                &[],
                            ),
                        ],
                    ),
                ],
            )
        };

        let at_r =
            angle_equal("Q", "R", "P", "T", "U", "S", &given(3), &given(5), &third);
        let at_p =
            angle_equal("R", "P", "Q", "U", "S", "T", &given(5), &third, &given(3));

        let congruent = b.ap(
            "jca",
            &binds! {"ph" => b.wff(&whole),
            "ps" => b.wff(&format!("( ( ( ( {same_pq} /\\ {same_qr} ) /\\ {same_rp} ) /\\ {ang_q} ) /\\ {ang_r} )")),
            "ch" => b.wff(&ang_p)},
            &[
                &b.ap(
                    "jca",
                    &binds! {"ph" => b.wff(&whole),
                    "ps" => b.wff(&format!("( ( ( {same_pq} /\\ {same_qr} ) /\\ {same_rp} ) /\\ {ang_q} )")),
                    "ch" => b.wff(&ang_r)},
                    &[
                        &b.ap(
                            "jca",
                            &binds! {"ph" => b.wff(&whole),
                            "ps" => b.wff(&format!("( ( {same_pq} /\\ {same_qr} ) /\\ {same_rp} )")),
                            "ch" => b.wff(&ang_q)},
                            &[
                                &b.ap(
                                    "jca31",
                                    &binds! {"ph" => b.wff(&whole), "ps" => b.wff(&same_pq),
                                    "ch" => b.wff(&same_qr),
                                    "th" => b.wff(&same_rp)},
                                    &[&given(3), &given(5), &third],
                                ),
                                &given(4),
                            ],
                        ),
                        &at_r,
                    ],
                ),
                &at_p,
            ],
        );

        // The six antecedents come off one at a time, outermost last.
        let mut proof = congruent;
        let mut claim = format!(
            "( ( ( ( ( {same_pq} /\\ {same_qr} ) /\\ {same_rp} ) /\\ {ang_q} ) /\\ {ang_r} ) /\\ {ang_p} )"
        );
        for i in (1..levels.len()).rev() {
            proof = b.ap(
                "ex",
                &binds! {"ph" => b.wff(&ws[i - 1]), "ps" => b.wff(&levels[i]),
                "ch" => b.wff(&claim)},
                &[&proof],
            );
            claim = format!("( {} -> {claim} )", levels[i]);
        }
        (proof, format!("|- ( {pts} -> {claim} )"))
    };
    out.push(Lemma::new("gsas", says.clone(), proof));
    b.define("gsas", &says);
}

pub const HEAD: &str =
    "$( Geometry: what this corpus needs of the plane and set.mm does not
   state. Points are complex numbers, distance is the absolute value of a
   difference, and the angle is the constant definitions.mm introduces,
   so everything here is a theorem rather than an axiom: CC is a model
   and nothing in it has to be assumed.  GEOMETRY.md takes that
   decision and says what it costs. $)

$( `angval` reads a value of the angle by substituting for the two names
   `df-ang` binds, and asks that they be free of what is substituted. They
   appear in no statement here, only inside the proofs. The pairs are
   written one at a time because `$d x y A B` would also hold A and B
   apart, and the lemmas below are applied at terms that share names. $)
$d x y $.
$d x A $.  $d y A $.
$d x B $.  $d y B $.
$d x C $.  $d y C $.
$d x P $.  $d y P $.
$d x Q $.  $d y Q $.
$d x R $.  $d y R $.
$d x S $.  $d y S $.
$d x T $.  $d y T $.
$d x U $.  $d y U $.

";

/// Each geometry lemma, in the order a later one may take an earlier.
pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    let mut out = triangle_lemmas(b);
    rotation(b, &mut out);
    angle_symmetry(b, &mut out);
    angle_size(b, &mut out);
    angle_bounds(b, &mut out);
    law_of_cosines(b, &mut out);
    cancelling(b, &mut out);
    side_angle_side(b, &mut out);
    out
}

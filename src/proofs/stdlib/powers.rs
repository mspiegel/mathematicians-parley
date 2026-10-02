//! Powers of 2, 3 and 5, for `proved.mm`.
//!
//! That ℚ is countable codes a rational by the product 2^a·3^b·5^c, and
//! asks that the product give back its exponents: a number has one
//! factorisation into primes. set.mm says it through how many times a
//! prime divides a number, `pCnt`. The count of p in a product is the sum
//! of its counts in the factors (`pcmul`), in p's own power it is the
//! exponent (`pcidlem`), and in another prime's power it is 0, since p does
//! not divide that prime (`pcexp`, `pceq0`, `dvdsprm`). So the count of 2 in
//! 2^a·3^b·5^c is a, and two equal products have equal counts.

use crate::binds;
use crate::mm::{Builder, Proof};
use crate::proofs::Lemma;

pub const HEAD: &str =
    "$( Powers: the exponents of 2, 3 and 5 in 2^a 3^b 5^c are a, b and c. $)\n\n";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    let mut out = vec![other_prime(b), product_count(b)];
    for k in 0..3 {
        out.push(count(b, k));
    }
    for k in 0..3 {
        out.push(exponent(b, k));
    }
    out
}

/// The three primes, the letters their exponents take in the product, and
/// the letters of the other product's.
const PRIMES: [&str; 3] = ["2", "3", "5"];
const OURS: [&str; 3] = ["A", "B", "C"];
const THEIRS: [&str; 3] = ["D", "E", "F"];

/// ( ( 2 ^ a ) x. ( 3 ^ b ) ) x. ( 5 ^ c ), of the three letters given.
fn product(letters: &[&str; 3]) -> String {
    format!(
        "( ( ( 2 ^ {} ) x. ( 3 ^ {} ) ) x. ( 5 ^ {} ) )",
        letters[0], letters[1], letters[2]
    )
}

/// Register a lemma's hypotheses, so its proof may rest on them.
fn hypotheses(b: &mut Builder, hyps: &[(&str, &str)]) {
    for (label, statement) in hyps {
        b.hypothesis(label, statement);
    }
}

/// Register a lemma so a later one may apply it, and give it back.
fn lemma(
    b: &mut Builder,
    label: &str,
    statement: &str,
    hyps: &[(&str, &str)],
    proof: Proof,
) -> Lemma {
    let said: Vec<&str> = hyps.iter().map(|(_, s)| *s).collect();
    b.define_with_hyps(label, statement, &said);
    Lemma::new(label, statement, proof).with_hyps(hyps)
}

/// ( ph -> what ) from a closed theorem.
fn always(b: &Builder, what: &str, proof: &Proof) -> Proof {
    b.ap(
        "a1i",
        &binds! {"ph" => b.wff(what), "ps" => b.wff("ph")},
        &[proof],
    )
}

/// ( ph -> P e. Prime ) for one of the three primes.
fn prime(b: &Builder, p: &str) -> Proof {
    always(b, &format!("{p} e. Prime"), &b.step(&format!("{p}prm")))
}

/// ( ph -> p =/= q ) for two of the three primes, from the smaller being
/// less (`2lt3`, `2lt5`, `3lt5`).
fn apart(b: &Builder, p: &str, q: &str) -> Proof {
    let (low, high) = if p < q { (p, q) } else { (q, p) };
    let below = b.ap(
        "ltneii",
        &binds! {"A" => b.class(low), "B" => b.class(high)},
        &[
            &b.step(&format!("{low}re")),
            &b.step(&format!("{low}lt{high}")),
        ],
    );
    let said = if p < q {
        below
    } else {
        b.ap(
            "necomi",
            &binds! {"A" => b.class(low), "B" => b.class(high)},
            &[&below],
        )
    };
    always(b, &format!("{p} =/= {q}"), &said)
}

/// `gpcoth`: a prime divides another prime's powers no times.
fn other_prime(b: &mut Builder) -> Lemma {
    let p = ("gpcoth.1", "|- ( ph -> P e. Prime )");
    let q = ("gpcoth.2", "|- ( ph -> Q e. Prime )");
    let ne = ("gpcoth.3", "|- ( ph -> P =/= Q )");
    let n = ("gpcoth.4", "|- ( ph -> N e. NN0 )");
    let statement = "|- ( ph -> ( P pCnt ( Q ^ N ) ) = 0 )";
    let all = [p, q, ne, n];
    hypotheses(b, &all);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let q_nat = b.ap(
            "syl",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("Q e. Prime"), "ch" => b.wff("Q e. NN")},
            &[&b.step(q.0), &b.ap("prmnn", &binds! {"P" => b.class("Q")}, &[])],
        );
        let divides = b.ap(
            "syl2anc",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("P e. ( ZZ>= ` 2 )"),
            "ch" => b.wff("Q e. Prime"), "th" => b.wff("( P || Q <-> P = Q )")},
            &[
                &b.ap(
                    "syl",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff("P e. Prime"),
                    "ch" => b.wff("P e. ( ZZ>= ` 2 )")},
                    &[
                        &b.step(p.0),
                        &b.ap("prmuz2", &binds! {"P" => b.class("P")}, &[]),
                    ],
                ),
                &b.step(q.0),
                &b.ap(
                    "dvdsprm",
                    &binds! {"N" => b.class("P"), "P" => b.class("Q")},
                    &[],
                ),
            ],
        );
        let not_divides = b.ap(
            "mtbird",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("P || Q"), "ch" => b.wff("P = Q")},
            &[
                &b.ap(
                    "neneqd",
                    &binds! {"ph" => ph.clone(), "A" => b.class("P"), "B" => b.class("Q")},
                    &[&b.step(ne.0)],
                ),
                &divides,
            ],
        );
        let none = b.ap(
            "mpbird",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("( P pCnt Q ) = 0"),
            "ch" => b.wff("-. P || Q")},
            &[
                &not_divides,
                &b.ap(
                    "syl2anc",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff("P e. Prime"),
                    "ch" => b.wff("Q e. NN"),
                    "th" => b.wff("( ( P pCnt Q ) = 0 <-> -. P || Q )")},
                    &[
                        &b.step(p.0),
                        &q_nat,
                        &b.ap(
                            "pceq0",
                            &binds! {"P" => b.class("P"), "N" => b.class("Q")},
                            &[],
                        ),
                    ],
                ),
            ],
        );
        let rational = b.ap(
            "jca",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("Q e. QQ"), "ch" => b.wff("Q =/= 0")},
            &[
                &b.ap(
                    "syl",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff("Q e. ZZ"),
                    "ch" => b.wff("Q e. QQ")},
                    &[
                        &b.ap(
                            "nnzd",
                            &binds! {"ph" => ph.clone(), "A" => b.class("Q")},
                            &[&q_nat],
                        ),
                        &b.ap("zq", &binds! {"A" => b.class("Q")}, &[]),
                    ],
                ),
                &b.ap(
                    "nnne0d",
                    &binds! {"ph" => ph.clone(), "A" => b.class("Q")},
                    &[&q_nat],
                ),
            ],
        );
        let power = b.ap(
            "syl3anc",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("P e. Prime"),
            "ch" => b.wff("( Q e. QQ /\\ Q =/= 0 )"), "th" => b.wff("N e. ZZ"),
            "ta" => b.wff("( P pCnt ( Q ^ N ) ) = ( N x. ( P pCnt Q ) )")},
            &[
                &b.step(p.0),
                &rational,
                &b.ap(
                    "nn0zd",
                    &binds! {"ph" => ph.clone(), "A" => b.class("N")},
                    &[&b.step(n.0)],
                ),
                &b.ap(
                    "pcexp",
                    &binds! {"P" => b.class("P"), "A" => b.class("Q"), "N" => b.class("N")},
                    &[],
                ),
            ],
        );
        let times_none = b.ap(
            "oveq2d",
            &binds! {"ph" => ph.clone(), "A" => b.class("( P pCnt Q )"), "B" => b.class("0"),
            "C" => b.class("N"), "F" => b.class("x.")},
            &[&none],
        );
        let zero = b.ap(
            "mul01d",
            &binds! {"ph" => ph.clone(), "A" => b.class("N")},
            &[&b.ap(
                "nn0cnd",
                &binds! {"ph" => ph.clone(), "A" => b.class("N")},
                &[&b.step(n.0)],
            )],
        );
        b.ap(
            "3eqtrd",
            &binds! {"ph" => ph, "A" => b.class("( P pCnt ( Q ^ N ) )"),
            "B" => b.class("( N x. ( P pCnt Q ) )"), "C" => b.class("( N x. 0 )"),
            "D" => b.class("0")},
            &[&power, &times_none, &zero],
        )
    };
    lemma(b, "gpcoth", statement, &all, proof)
}

/// `gpcmul3`: a prime's count in a product of three natural numbers is
/// the sum of its counts in each.
fn product_count(b: &mut Builder) -> Lemma {
    let p = ("gpcmul3.1", "|- ( ph -> P e. Prime )");
    let x = ("gpcmul3.2", "|- ( ph -> X e. NN )");
    let y = ("gpcmul3.3", "|- ( ph -> Y e. NN )");
    let z = ("gpcmul3.4", "|- ( ph -> Z e. NN )");
    let statement = "|- ( ph -> ( P pCnt ( ( X x. Y ) x. Z ) ) = \
                     ( ( ( P pCnt X ) + ( P pCnt Y ) ) + ( P pCnt Z ) ) )";
    let all = [p, x, y, z];
    hypotheses(b, &all);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let whole = |of: &str, natural: &Proof| {
            b.ap(
                "jca",
                &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{of} e. ZZ")),
                "ch" => b.wff(&format!("{of} =/= 0"))},
                &[
                    &b.ap(
                        "nnzd",
                        &binds! {"ph" => ph.clone(), "A" => b.class(of)},
                        &[natural],
                    ),
                    &b.ap(
                        "nnne0d",
                        &binds! {"ph" => ph.clone(), "A" => b.class(of)},
                        &[natural],
                    ),
                ],
            )
        };
        let split = |left: &str, right: &str, l: &Proof, r: &Proof| {
            b.ap(
                "syl3anc",
                &binds! {"ph" => ph.clone(), "ps" => b.wff("P e. Prime"),
                "ch" => b.wff(&format!("( {left} e. ZZ /\\ {left} =/= 0 )")),
                "th" => b.wff(&format!("( {right} e. ZZ /\\ {right} =/= 0 )")),
                "ta" => b.wff(&format!(
                    "( P pCnt ( {left} x. {right} ) ) = ( ( P pCnt {left} ) + ( P pCnt {right} ) )"
                ))},
                &[
                    &b.step(p.0),
                    &whole(left, l),
                    &whole(right, r),
                    &b.ap(
                        "pcmul",
                        &binds! {"P" => b.class("P"), "A" => b.class(left), "B" => b.class(right)},
                        &[],
                    ),
                ],
            )
        };
        let xy = b.ap(
            "nnmulcld",
            &binds! {"ph" => ph.clone(), "A" => b.class("X"), "B" => b.class("Y")},
            &[&b.step(x.0), &b.step(y.0)],
        );
        let outer = split("( X x. Y )", "Z", &xy, &b.step(z.0));
        let inner = split("X", "Y", &b.step(x.0), &b.step(y.0));
        let rewritten = b.ap(
            "oveq1d",
            &binds! {"ph" => ph.clone(), "A" => b.class("( P pCnt ( X x. Y ) )"),
            "B" => b.class("( ( P pCnt X ) + ( P pCnt Y ) )"),
            "C" => b.class("( P pCnt Z )"), "F" => b.class("+")},
            &[&inner],
        );
        b.ap(
            "eqtrd",
            &binds! {"ph" => ph, "A" => b.class("( P pCnt ( ( X x. Y ) x. Z ) )"),
            "B" => b.class("( ( P pCnt ( X x. Y ) ) + ( P pCnt Z ) )"),
            "C" => b.class("( ( ( P pCnt X ) + ( P pCnt Y ) ) + ( P pCnt Z ) )")},
            &[&outer, &rewritten],
        )
    };
    lemma(b, "gpcmul3", statement, &all, proof)
}

/// The three exponents' hypotheses, under a lemma's label.
fn exponents(label: &str, letters: &[&str; 3]) -> Vec<(String, String)> {
    letters
        .iter()
        .enumerate()
        .map(|(i, l)| {
            (
                format!("{label}.{}", i + 1),
                format!("|- ( ph -> {l} e. NN0 )"),
            )
        })
        .collect()
}

/// `gpc2`, `gpc3`, `gpc5`: the count of each of the three primes in
/// 2^a·3^b·5^c is its exponent.
fn count(b: &mut Builder, k: usize) -> Lemma {
    let p = PRIMES[k];
    let label = format!("gpc{p}");
    let hyps = exponents(&label, &OURS);
    let said: Vec<(&str, &str)> =
        hyps.iter().map(|(l, s)| (l.as_str(), s.as_str())).collect();
    let statement =
        format!("|- ( ph -> ( {p} pCnt {} ) = {} )", product(&OURS), OURS[k]);
    hypotheses(b, &said);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let powers: Vec<String> = (0..3)
            .map(|j| format!("( {} ^ {} )", PRIMES[j], OURS[j]))
            .collect();
        let natural = |j: usize| {
            b.ap(
                "nnexpcld",
                &binds! {"ph" => ph.clone(), "A" => b.class(PRIMES[j]), "N" => b.class(OURS[j])},
                &[
                    &always(b, &format!("{} e. NN", PRIMES[j]), &b.step(&format!("{}nn", PRIMES[j]))),
                    &b.step(said[j].0),
                ],
            )
        };
        let split = b.ap(
            "gpcmul3",
            &binds! {"ph" => ph.clone(), "P" => b.class(p), "X" => b.class(&powers[0]),
            "Y" => b.class(&powers[1]), "Z" => b.class(&powers[2])},
            &[&prime(b, p), &natural(0), &natural(1), &natural(2)],
        );
        // Each factor's count: its exponent in p's own power, 0 in another's.
        let value = |j: usize| {
            if j == k {
                OURS[j].to_string()
            } else {
                "0".to_string()
            }
        };
        let term = |j: usize| {
            if j == k {
                b.ap(
                    "syl2anc",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{p} e. Prime")),
                    "ch" => b.wff(&format!("{} e. NN0", OURS[j])),
                    "th" => b.wff(&format!("( {p} pCnt {} ) = {}", powers[j], OURS[j]))},
                    &[
                        &prime(b, p),
                        &b.step(said[j].0),
                        &b.ap(
                            "pcidlem",
                            &binds! {"P" => b.class(p), "A" => b.class(OURS[j])},
                            &[],
                        ),
                    ],
                )
            } else {
                b.ap(
                    "gpcoth",
                    &binds! {"ph" => ph.clone(), "P" => b.class(p), "Q" => b.class(PRIMES[j]),
                    "N" => b.class(OURS[j])},
                    &[&prime(b, p), &prime(b, PRIMES[j]), &apart(b, p, PRIMES[j]), &b.step(said[j].0)],
                )
            }
        };
        let count_of = |j: usize| format!("( {p} pCnt {} )", powers[j]);
        let inner = b.ap(
            "oveq12d",
            &binds! {"ph" => ph.clone(), "A" => b.class(&count_of(0)), "B" => b.class(&value(0)),
            "C" => b.class(&count_of(1)), "D" => b.class(&value(1)), "F" => b.class("+")},
            &[&term(0), &term(1)],
        );
        let first_two = format!("( {} + {} )", count_of(0), count_of(1));
        let values_two = format!("( {} + {} )", value(0), value(1));
        let outer = b.ap(
            "oveq12d",
            &binds! {"ph" => ph.clone(), "A" => b.class(&first_two), "B" => b.class(&values_two),
            "C" => b.class(&count_of(2)), "D" => b.class(&value(2)), "F" => b.class("+")},
            &[&inner, &term(2)],
        );
        let sum = format!("( {values_two} + {} )", value(2));
        // The sum of one exponent and two zeros is the exponent.
        let letter = OURS[k];
        let complex = b.ap(
            "nn0cnd",
            &binds! {"ph" => ph.clone(), "A" => b.class(letter)},
            &[&b.step(said[k].0)],
        );
        let simplified = match k {
            0 => b.ap(
                "eqtrd",
                &binds! {"ph" => ph.clone(), "A" => b.class(&sum),
                "B" => b.class(&format!("( {letter} + 0 )")), "C" => b.class(letter)},
                &[
                    &b.ap(
                        "addridd",
                        &binds! {"ph" => ph.clone(), "A" => b.class(&values_two)},
                        &[&b.ap(
                            "addcld",
                            &binds! {"ph" => ph.clone(), "A" => b.class(letter),
                            "B" => b.class("0")},
                            &[&complex, &always(b, "0 e. CC", &b.step("0cn"))],
                        )],
                    ),
                    &b.ap("addridd", &binds! {"ph" => ph.clone(), "A" => b.class(letter)}, &[&complex]),
                ],
            ),
            1 => b.ap(
                "eqtrd",
                &binds! {"ph" => ph.clone(), "A" => b.class(&sum),
                "B" => b.class(&format!("( 0 + {letter} )")), "C" => b.class(letter)},
                &[
                    &b.ap(
                        "addridd",
                        &binds! {"ph" => ph.clone(), "A" => b.class(&values_two)},
                        &[&b.ap(
                            "addcld",
                            &binds! {"ph" => ph.clone(), "A" => b.class("0"),
                            "B" => b.class(letter)},
                            &[&always(b, "0 e. CC", &b.step("0cn")), &complex],
                        )],
                    ),
                    &b.ap("addlidd", &binds! {"ph" => ph.clone(), "A" => b.class(letter)}, &[&complex]),
                ],
            ),
            _ => b.ap(
                "eqtrd",
                &binds! {"ph" => ph.clone(), "A" => b.class(&sum),
                "B" => b.class(&format!("( 0 + {letter} )")), "C" => b.class(letter)},
                &[
                    &b.ap(
                        "oveq1d",
                        &binds! {"ph" => ph.clone(), "A" => b.class("( 0 + 0 )"),
                        "B" => b.class("0"), "C" => b.class(letter), "F" => b.class("+")},
                        &[&always(b, "( 0 + 0 ) = 0", &b.step("00id"))],
                    ),
                    &b.ap("addlidd", &binds! {"ph" => ph.clone(), "A" => b.class(letter)}, &[&complex]),
                ],
            ),
        };
        let counts = format!("( {first_two} + {} )", count_of(2));
        b.ap(
            "3eqtrd",
            &binds! {"ph" => ph, "A" => b.class(&format!("( {p} pCnt {} )", product(&OURS))),
            "B" => b.class(&counts), "C" => b.class(&sum), "D" => b.class(letter)},
            &[&split, &outer, &simplified],
        )
    };
    lemma(b, &label, &statement, &said, proof)
}

/// `g235a`, `g235b`, `g235c`: for `thm:stdlib/divisibility/prime-powers-unique`,
/// one to a sentence: two equal products of powers of 2, 3 and 5 have each
/// exponent the same.
fn exponent(b: &mut Builder, k: usize) -> Lemma {
    let p = PRIMES[k];
    let label = format!("g235{}", ["a", "b", "c"][k]);
    let mut hyps = exponents(&label, &OURS);
    for (i, l) in THEIRS.iter().enumerate() {
        hyps.push((
            format!("{label}.{}", i + 4),
            format!("|- ( ph -> {l} e. NN0 )"),
        ));
    }
    hyps.push((
        format!("{label}.7"),
        format!("|- ( ph -> {} = {} )", product(&OURS), product(&THEIRS)),
    ));
    let said: Vec<(&str, &str)> =
        hyps.iter().map(|(l, s)| (l.as_str(), s.as_str())).collect();
    let statement = format!("|- ( ph -> {} = {} )", OURS[k], THEIRS[k]);
    hypotheses(b, &said);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let count_of = |letters: &[&str; 3], at: usize| {
            b.ap(
                &format!("gpc{p}"),
                &binds! {"ph" => ph.clone(), "A" => b.class(letters[0]),
                "B" => b.class(letters[1]), "C" => b.class(letters[2])},
                &[
                    &b.step(said[at].0),
                    &b.step(said[at + 1].0),
                    &b.step(said[at + 2].0),
                ],
            )
        };
        let same = b.ap(
            "oveq2d",
            &binds! {"ph" => ph.clone(), "A" => b.class(&product(&OURS)),
            "B" => b.class(&product(&THEIRS)), "C" => b.class(p), "F" => b.class("pCnt")},
            &[&b.step(said[6].0)],
        );
        b.ap(
            "3eqtr3d",
            &binds! {"ph" => ph.clone(), "A" => b.class(&format!("( {p} pCnt {} )", product(&OURS))),
            "B" => b.class(&format!("( {p} pCnt {} )", product(&THEIRS))),
            "C" => b.class(OURS[k]), "D" => b.class(THEIRS[k])},
            &[&same, &count_of(&OURS, 0), &count_of(&THEIRS, 3)],
        )
    };
    lemma(b, &label, &statement, &said, proof)
}

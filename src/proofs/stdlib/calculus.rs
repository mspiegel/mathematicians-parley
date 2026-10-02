//! Calculus, for `proved.mm`.
//!
//! The mean value theorem asks what a textbook calls the sum rules: a sum of
//! continuous functions is continuous, a line is, and the derivative of a sum
//! is the sum of the derivatives, of a line its slope. set.mm says each of a
//! map written out, `( x e. X |-> A )`, or of functions added pointwise,
//! `( F oF + G )`, and the page says it of functions named apart from their
//! values, F with F(x) = f(x) + g(x) for every x. Each lemma here is the
//! page's form: the function is its map (`dffn5`) or the pointwise sum
//! (`offval`), and set.mm's rule is applied to that.
//!
//! The derivative rules hold on any D ⊆ ℝ. A sum is differentiable at each
//! point both its parts are (`dvaddbr`), so its rule asks nothing of the set
//! U it is said on. A line is differentiable at a point of D only where a
//! neighbourhood of it lies in D, so its rule asks U be open (`dvres`,
//! `isopn3i`), as a textbook's does.
//!
//! A function on [a, b] is differentiable on (a, b) at most, since a
//! derivative is taken only where a neighbourhood lies in the domain
//! (`dvbssntr`, `iccntr`, `gdvsub`). The page's "differentiable on (a, b)"
//! says (a, b) lies within the derivative's domain, and for a function on
//! [a, b] that makes the two equal (`gdvdmicc`), which is what set.mm's
//! `rolle` asks (`grolle`). Derivatives are into ℂ in set.mm, and a real
//! function's are real (`dvfre`).
//!
//! Continuity in set.mm is into a set named by the space, `D -cn-> CC` for
//! the rules and `D -cn-> RR` for the page; `cncfss` widens one to the other
//! and `cncfcdm` narrows a continuous function into ℝ when its values are.

use crate::binds;
use crate::mm::{Builder, Proof};
use crate::proofs::Lemma;

pub const HEAD: &str =
    "$( Calculus: continuity and derivatives of a sum and of a line, as the
   page says them of functions named apart from their values. $)
$d x ph $.
$d x A $.
$d x B $.
$d x D $.
$d x F $.
$d x G $.
$d x H $.
$d x I $.
$d x M $.
$d x U $.
$d x V $.

";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![
        domain(b),
        values(b),
        inside_open(b),
        exactly_open(b),
        rolle(b),
        derivative_type(b),
        derivative_real(b),
        sum_pointwise(b),
        sum_at(b),
        sum_domain(b),
        sum_values(b),
        line_restricted(b),
        line_domain(b),
        line_values(b),
        continuous_line(b),
        continuous_sum(b),
    ]
}

const AB: &str = "( A [,] B )";
const OPEN: &str = "( A (,) B )";
const K: &str = "( TopOpen ` CCfld )";
const T: &str = "( topGen ` ran (,) )";

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

/// Hypotheses under labels of a lemma's own, from statements shared by
/// several lemmas.
fn labelled(label: &str, statements: &[&'static str]) -> Vec<(String, &'static str)> {
    statements
        .iter()
        .enumerate()
        .map(|(i, s)| (format!("{label}.{}", i + 1), *s))
        .collect()
}

fn pairs<'a>(hyps: &'a [(String, &'static str)]) -> Vec<(&'a str, &'static str)> {
    hyps.iter().map(|(l, s)| (l.as_str(), *s)).collect()
}

/// ( ( ph /\ x e. U ) -> what ) from ( ph -> what ).
fn at_point(b: &Builder, what: &str, proof: &Proof) -> Proof {
    b.ap(
        "adantr",
        &binds! {"ph" => b.wff("ph"), "ps" => b.wff(what), "ch" => b.wff("x e. U")},
        &[proof],
    )
}

/// `gdvdm`: a map on I is defined on I.
fn domain(b: &mut Builder) -> Lemma {
    let is_map = ("gdvdm.1", "|- ( ph -> D = ( x e. I |-> E ) )");
    let a_set = ("gdvdm.2", "|- ( ( ph /\\ x e. I ) -> E e. V )");
    let statement = "|- ( ph -> I C_ dom D )";
    hypotheses(b, &[is_map, a_set]);
    let proof = {
        let b: &Builder = b;
        let x = b.float("x");
        let map = "( x e. I |-> E )";
        let every = b.ap(
            "ralrimiva",
            &binds! {"ph" => b.wff("ph"), "ps" => b.wff("E e. V"), "x" => x.clone(),
            "A" => b.class("I")},
            &[&b.step(a_set.0)],
        );
        let map_domain = b.ap(
            "syl",
            &binds! {"ph" => b.wff("ph"), "ps" => b.wff("A. x e. I E e. V"),
            "ch" => b.wff(&format!("dom {map} = I"))},
            &[
                &every,
                &b.ap(
                    "dmmptg",
                    &binds! {"x" => x.clone(), "A" => b.class("I"), "B" => b.class("E"),
                    "V" => b.class("V")},
                    &[],
                ),
            ],
        );
        let exactly = b.ap(
            "eqtrd",
            &binds! {"ph" => b.wff("ph"), "A" => b.class("dom D"),
            "B" => b.class(&format!("dom {map}")), "C" => b.class("I")},
            &[
                &b.ap(
                    "dmeqd",
                    &binds! {"ph" => b.wff("ph"), "A" => b.class("D"), "B" => b.class(map)},
                    &[&b.step(is_map.0)],
                ),
                &map_domain,
            ],
        );
        b.ap(
            "eqimssd",
            &binds! {"ph" => b.wff("ph"), "A" => b.class("I"), "B" => b.class("dom D")},
            &[&b.ap(
                "eqcomd",
                &binds! {"ph" => b.wff("ph"), "A" => b.class("dom D"), "B" => b.class("I")},
                &[&exactly],
            )],
        )
    };
    lemma(b, "gdvdm", statement, &[is_map, a_set], proof)
}

/// `gdvval`: the value of a map on I at each x there is its rule.
fn values(b: &mut Builder) -> Lemma {
    let is_map = ("gdvval.1", "|- ( ph -> D = ( x e. I |-> E ) )");
    let a_set = ("gdvval.2", "|- ( ( ph /\\ x e. I ) -> E e. V )");
    let statement = "|- ( ph -> A. x e. I ( D ` x ) = E )";
    hypotheses(b, &[is_map, a_set]);
    let proof = {
        let b: &Builder = b;
        let x = b.float("x");
        let map = "( x e. I |-> E )";
        let at = "( ph /\\ x e. I )";
        let applied = b.ap(
            "fveq1d",
            &binds! {"ph" => b.wff(at), "F" => b.class("D"), "G" => b.class(map),
            "A" => b.class("x")},
            &[&b.ap(
                "adantr",
                &binds! {"ph" => b.wff("ph"), "ps" => b.wff(&format!("D = {map}")),
                "ch" => b.wff("x e. I")},
                &[&b.step(is_map.0)],
            )],
        );
        let rule = b.ap(
            "syl2anc",
            &binds! {"ph" => b.wff(at), "ps" => b.wff("x e. I"), "ch" => b.wff("E e. V"),
            "th" => b.wff(&format!("( {map} ` x ) = E"))},
            &[
                &b.ap(
                    "simpr",
                    &binds! {"ph" => b.wff("ph"), "ps" => b.wff("x e. I")},
                    &[],
                ),
                &b.step(a_set.0),
                &b.ap(
                    "fvmpt2",
                    &binds! {"x" => x.clone(), "A" => b.class("I"), "B" => b.class("E"),
                    "C" => b.class("V"), "F" => b.class(map)},
                    &[&b.ap("eqid", &binds! {"A" => b.class(map)}, &[])],
                ),
            ],
        );
        let value = b.ap(
            "eqtrd",
            &binds! {"ph" => b.wff(at), "A" => b.class("( D ` x )"),
            "B" => b.class(&format!("( {map} ` x )")), "C" => b.class("E")},
            &[&applied, &rule],
        );
        b.ap(
            "ralrimiva",
            &binds! {"ph" => b.wff("ph"), "ps" => b.wff("( D ` x ) = E"), "x" => x,
            "A" => b.class("I")},
            &[&value],
        )
    };
    lemma(b, "gdvval", statement, &[is_map, a_set], proof)
}

/// ( ph -> RR C_ CC )
fn real_complex(b: &Builder) -> Proof {
    b.ap(
        "a1i",
        &binds! {"ph" => b.wff("RR C_ CC"), "ps" => b.wff("ph")},
        &[&b.step("ax-resscn")],
    )
}

/// ( ph -> RR e. { RR , CC } )
fn over_reals(b: &Builder, ph: &str) -> Proof {
    b.ap(
        "a1i",
        &binds! {"ph" => b.wff("RR e. { RR , CC }"), "ps" => b.wff(ph)},
        &[&b.step("reelprrecn")],
    )
}

/// ( ph -> ( A [,] B ) C_ RR ), from the two endpoints' hypotheses.
fn closed_real(b: &Builder, a: &str, bb: &str) -> Proof {
    b.ap(
        "syl2anc",
        &binds! {"ph" => b.wff("ph"), "ps" => b.wff("A e. RR"), "ch" => b.wff("B e. RR"),
        "th" => b.wff(&format!("{AB} C_ RR"))},
        &[
            &b.step(a),
            &b.step(bb),
            &b.ap(
                "iccssre",
                &binds! {"A" => b.class("A"), "B" => b.class("B")},
                &[],
            ),
        ],
    )
}

/// |- ( topGen ` ran (,) ) = ( ( TopOpen ` CCfld ) |`t RR )
fn real_topology(b: &Builder) -> Proof {
    b.ap(
        "tgioo2",
        &binds! {"J" => b.class(K)},
        &[&b.ap("eqid", &binds! {"A" => b.class(K)}, &[])],
    )
}

/// ( ph -> f : D --> CC ) from f into ℝ.
fn into_complex(b: &Builder, f: &str, domain: &str, typed: &Proof) -> Proof {
    b.ap(
        "fssd",
        &binds! {"ph" => b.wff("ph"), "F" => b.class(f), "A" => b.class(domain),
        "B" => b.class("RR"), "C" => b.class("CC")},
        &[typed, &real_complex(b)],
    )
}

/// |- Fun ( RR _D f ): a derivative is a function, into ℂ (`dvf`).
fn derivative_function(b: &Builder, f: &str) -> Proof {
    let d = format!("( RR _D {f} )");
    b.ap(
        "ax-mp",
        &binds! {"ph" => b.wff(&format!("{d} : dom {d} --> CC")),
        "ps" => b.wff(&format!("Fun {d}"))},
        &[
            &b.ap("dvf", &binds! {"F" => b.class(f)}, &[]),
            &b.ap(
                "ffun",
                &binds! {"F" => b.class(&d), "A" => b.class(&format!("dom {d}")),
                "B" => b.class("CC")},
                &[],
            ),
        ],
    )
}

/// `gdvsub`: a function on [a, b] has a derivative on (a, b) at most, since
/// a derivative is taken only where a neighbourhood lies in the domain.
fn inside_open(b: &mut Builder) -> Lemma {
    let a = ("gdvsub.1", "|- ( ph -> A e. RR )");
    let bb = ("gdvsub.2", "|- ( ph -> B e. RR )");
    let f = ("gdvsub.3", "|- ( ph -> F : ( A [,] B ) --> CC )");
    let statement = "|- ( ph -> dom ( RR _D F ) C_ ( A (,) B ) )";
    hypotheses(b, &[a, bb, f]);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let closed_inside = format!("( ( int ` {T} ) ` {AB} )");
        let within = b.ap(
            "dvbssntr",
            &binds! {"ph" => ph.clone(), "S" => b.class("RR"), "F" => b.class("F"),
            "A" => b.class(AB), "J" => b.class(T), "K" => b.class(K)},
            &[
                &real_complex(b),
                &b.step(f.0),
                &closed_real(b, a.0, bb.0),
                &real_topology(b),
                &b.ap("eqid", &binds! {"A" => b.class(K)}, &[]),
            ],
        );
        let interior_closed = b.ap(
            "syl2anc",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("A e. RR"), "ch" => b.wff("B e. RR"),
            "th" => b.wff(&format!("{closed_inside} = {OPEN}"))},
            &[
                &b.step(a.0),
                &b.step(bb.0),
                &b.ap(
                    "iccntr",
                    &binds! {"A" => b.class("A"), "B" => b.class("B")},
                    &[],
                ),
            ],
        );
        b.ap(
            "sseqtrd",
            &binds! {"ph" => ph, "A" => b.class("dom ( RR _D F )"),
            "B" => b.class(&closed_inside), "C" => b.class(OPEN)},
            &[&within, &interior_closed],
        )
    };
    lemma(b, "gdvsub", statement, &[a, bb, f], proof)
}

/// `gdvdmicc`: a function on [a, b] differentiable on (a, b) is
/// differentiable there and nowhere else, which is the form set.mm's
/// `rolle` and `mvth` ask.
fn exactly_open(b: &mut Builder) -> Lemma {
    let a = ("gdvdmicc.1", "|- ( ph -> A e. RR )");
    let bb = ("gdvdmicc.2", "|- ( ph -> B e. RR )");
    let f = ("gdvdmicc.3", "|- ( ph -> F : ( A [,] B ) --> CC )");
    let d = ("gdvdmicc.4", "|- ( ph -> ( A (,) B ) C_ dom ( RR _D F ) )");
    let statement = "|- ( ph -> dom ( RR _D F ) = ( A (,) B ) )";
    hypotheses(b, &[a, bb, f, d]);
    let proof = {
        let b: &Builder = b;
        b.ap(
            "eqssd",
            &binds! {"ph" => b.wff("ph"), "A" => b.class("dom ( RR _D F )"),
            "B" => b.class(OPEN)},
            &[
                &b.ap(
                    "gdvsub",
                    &binds! {"ph" => b.wff("ph"), "A" => b.class("A"), "B" => b.class("B"),
                    "F" => b.class("F")},
                    &[&b.step(a.0), &b.step(bb.0), &b.step(f.0)],
                ),
                &b.step(d.0),
            ],
        )
    };
    lemma(b, "gdvdmicc", statement, &[a, bb, f, d], proof)
}

/// `grolle`: for `thm:stdlib/calculus/rolle`. set.mm's `rolle` asks the
/// derivative be defined on exactly (a, b), and the page says on (a, b).
fn rolle(b: &mut Builder) -> Lemma {
    let a = ("grolle.1", "|- ( ph -> A e. RR )");
    let bb = ("grolle.2", "|- ( ph -> B e. RR )");
    let lt = ("grolle.3", "|- ( ph -> A < B )");
    let f = ("grolle.4", "|- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )");
    let d = ("grolle.5", "|- ( ph -> ( A (,) B ) C_ dom ( RR _D F ) )");
    let e = ("grolle.6", "|- ( ph -> ( F ` A ) = ( F ` B ) )");
    let statement = "|- ( ph -> E. x e. ( A (,) B ) ( ( RR _D F ) ` x ) = 0 )";
    let all = [a, bb, lt, f, d, e];
    hypotheses(b, &all);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let into_rr = b.ap(
            "syl",
            &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("F e. ( {AB} -cn-> RR )")),
            "ch" => b.wff(&format!("F : {AB} --> RR"))},
            &[
                &b.step(f.0),
                &b.ap(
                    "cncff",
                    &binds! {"A" => b.class(AB), "B" => b.class("RR"), "F" => b.class("F")},
                    &[],
                ),
            ],
        );
        let exactly = b.ap(
            "gdvdmicc",
            &binds! {"ph" => ph.clone(), "A" => b.class("A"), "B" => b.class("B"),
            "F" => b.class("F")},
            &[
                &b.step(a.0),
                &b.step(bb.0),
                &into_complex(b, "F", AB, &into_rr),
                &b.step(d.0),
            ],
        );
        b.ap(
            "rolle",
            &binds! {"ph" => ph, "A" => b.class("A"), "B" => b.class("B"),
            "F" => b.class("F"), "x" => b.float("x")},
            &[
                &b.step(a.0),
                &b.step(bb.0),
                &b.step(lt.0),
                &b.step(f.0),
                &exactly,
                &b.step(e.0),
            ],
        )
    };
    lemma(b, "grolle", statement, &all, proof)
}

/// What `gdvf` and `gdvre` ask: a real function on [a, b] differentiable on
/// (a, b).
const ON_CLOSED: [&str; 4] = [
    "|- ( ph -> A e. RR )",
    "|- ( ph -> B e. RR )",
    "|- ( ph -> F : ( A [,] B ) --> RR )",
    "|- ( ph -> ( A (,) B ) C_ dom ( RR _D F ) )",
];

/// `gdvf`: a real function differentiable on (a, b) has a real derivative
/// there.
fn derivative_type(b: &mut Builder) -> Lemma {
    let hyps = labelled("gdvf", &ON_CLOSED);
    let said = pairs(&hyps);
    let statement = "|- ( ph -> ( RR _D F ) : ( A (,) B ) --> RR )";
    hypotheses(b, &said);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let onto_domain = "( RR _D F ) : dom ( RR _D F ) --> RR";
        let typed = b.ap(
            "syl2anc",
            &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("F : {AB} --> RR")),
            "ch" => b.wff(&format!("{AB} C_ RR")), "th" => b.wff(onto_domain)},
            &[
                &b.step(said[2].0),
                &closed_real(b, said[0].0, said[1].0),
                &b.ap(
                    "dvfre",
                    &binds! {"F" => b.class("F"), "A" => b.class(AB)},
                    &[],
                ),
            ],
        );
        let exactly = b.ap(
            "gdvdmicc",
            &binds! {"ph" => ph.clone(), "A" => b.class("A"), "B" => b.class("B"),
            "F" => b.class("F")},
            &[
                &b.step(said[0].0),
                &b.step(said[1].0),
                &into_complex(b, "F", AB, &b.step(said[2].0)),
                &b.step(said[3].0),
            ],
        );
        let moved = b.ap(
            "feq2d",
            &binds! {"ph" => ph.clone(), "A" => b.class("dom ( RR _D F )"),
            "B" => b.class(OPEN), "C" => b.class("RR"), "F" => b.class("( RR _D F )")},
            &[&exactly],
        );
        b.ap(
            "mpbid",
            &binds! {"ph" => ph, "ps" => b.wff(onto_domain),
            "ch" => b.wff(&format!("( RR _D F ) : {OPEN} --> RR"))},
            &[&typed, &moved],
        )
    };
    lemma(b, "gdvf", statement, &said, proof)
}

/// `gdvre`: for `mun:stdlib/calculus/derivative-real`.
fn derivative_real(b: &mut Builder) -> Lemma {
    let hyps = labelled("gdvre", &ON_CLOSED);
    let mut said = pairs(&hyps);
    said.push(("gdvre.5", "|- ( ph -> C e. ( A (,) B ) )"));
    let statement = "|- ( ph -> ( ( RR _D F ) ` C ) e. RR )";
    hypotheses(b, &said);
    let proof = {
        let b: &Builder = b;
        let typed = b.ap(
            "gdvf",
            &binds! {"ph" => b.wff("ph"), "A" => b.class("A"), "B" => b.class("B"),
            "F" => b.class("F")},
            &[
                &b.step(said[0].0),
                &b.step(said[1].0),
                &b.step(said[2].0),
                &b.step(said[3].0),
            ],
        );
        b.ap(
            "ffvelcdmd",
            &binds! {"ph" => b.wff("ph"), "F" => b.class("( RR _D F )"),
            "A" => b.class(OPEN), "B" => b.class("RR"), "C" => b.class("C")},
            &[&typed, &b.step(said[4].0)],
        )
    };
    lemma(b, "gdvre", statement, &said, proof)
}

/// ( ph -> f = ( x e. D |-> rule ) ), for f on D whose value at every x
/// there is the rule: `dffn5`, then the values rewritten.
fn as_rule(b: &Builder, f: &str, typed: &Proof, every: &Proof, rule: &str) -> Proof {
    let ph = b.wff("ph");
    let x = b.float("x");
    let values = format!("( x e. D |-> ( {f} ` x ) )");
    let ruled = format!("( x e. D |-> {rule} )");
    let said = format!("( {f} ` x ) = {rule}");
    let as_values = b.ap(
        "sylib",
        &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{f} Fn D")),
        "ch" => b.wff(&format!("{f} = {values}"))},
        &[
            &b.ap(
                "ffnd",
                &binds! {"ph" => ph.clone(), "F" => b.class(f), "A" => b.class("D"),
                "B" => b.class("RR")},
                &[typed],
            ),
            &b.ap(
                "dffn5",
                &binds! {"x" => x.clone(), "A" => b.class("D"), "F" => b.class(f)},
                &[],
            ),
        ],
    );
    let rewritten = b.ap(
        "mpteq2dva",
        &binds! {"ph" => ph.clone(), "x" => x.clone(), "A" => b.class("D"),
        "B" => b.class(&format!("( {f} ` x )")), "C" => b.class(rule)},
        &[&b.ap(
            "r19.21bi",
            &binds! {"ph" => ph.clone(), "ps" => b.wff(&said), "x" => x,
            "A" => b.class("D")},
            &[every],
        )],
    );
    b.ap(
        "eqtrd",
        &binds! {"ph" => ph, "A" => b.class(f), "B" => b.class(&values),
        "C" => b.class(&ruled)},
        &[&as_values, &rewritten],
    )
}

const SUM: &str = "( ( F ` x ) + ( G ` x ) )";
const ADDED: &str = "( F oF + G )";

/// `gdvaddof`: a function whose value at every x is the sum of two others'
/// is their pointwise sum.
fn sum_pointwise(b: &mut Builder) -> Lemma {
    let d = ("gdvaddof.1", "|- ( ph -> D C_ RR )");
    let h = ("gdvaddof.2", "|- ( ph -> H : D --> RR )");
    let f = ("gdvaddof.3", "|- ( ph -> F : D --> RR )");
    let g = ("gdvaddof.4", "|- ( ph -> G : D --> RR )");
    let rule = (
        "gdvaddof.5",
        "|- ( ph -> A. x e. D ( H ` x ) = ( ( F ` x ) + ( G ` x ) ) )",
    );
    let statement = "|- ( ph -> H = ( F oF + G ) )";
    let all = [d, h, f, g, rule];
    hypotheses(b, &all);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let x = b.float("x");
        let map = format!("( x e. D |-> {SUM} )");
        let at = "( ph /\\ x e. D )";
        let on = |name: &str, typed: &str| {
            b.ap(
                "ffnd",
                &binds! {"ph" => ph.clone(), "F" => b.class(name), "A" => b.class("D"),
                "B" => b.class("RR")},
                &[&b.step(typed)],
            )
        };
        let a_set = b.ap(
            "ssexd",
            &binds! {"ph" => ph.clone(), "A" => b.class("D"), "B" => b.class("RR"),
            "C" => b.class("_V")},
            &[
                &b.ap(
                    "a1i",
                    &binds! {"ph" => b.wff("RR e. _V"), "ps" => ph.clone()},
                    &[&b.step("reex")],
                ),
                &b.step(d.0),
            ],
        );
        let value = |name: &str| {
            b.ap(
                "eqidd",
                &binds! {"ph" => b.wff(at), "A" => b.class(&format!("( {name} ` x )"))},
                &[],
            )
        };
        let added = b.ap(
            "offval",
            &binds! {"ph" => ph.clone(), "F" => b.class("F"), "G" => b.class("G"),
            "A" => b.class("D"), "B" => b.class("D"), "V" => b.class("_V"),
            "W" => b.class("_V"), "S" => b.class("D"), "R" => b.class("+"),
            "C" => b.class("( F ` x )"), "D" => b.class("( G ` x )"), "x" => x},
            &[
                &on("F", f.0),
                &on("G", g.0),
                &a_set,
                &a_set,
                &b.ap("inidm", &binds! {"A" => b.class("D")}, &[]),
                &value("F"),
                &value("G"),
            ],
        );
        b.ap(
            "eqtr4d",
            &binds! {"ph" => ph, "A" => b.class("H"), "B" => b.class(&map),
            "C" => b.class(ADDED)},
            &[&as_rule(b, "H", &b.step(h.0), &b.step(rule.0), SUM), &added],
        )
    };
    lemma(b, "gdvaddof", statement, &all, proof)
}

/// `gdvaddbr`: at a point where two functions are differentiable, their
/// sum is, with the sum of their derivatives (`dvaddbr`). It names no bound
/// letter, so a lemma may apply it at a point it has fixed.
fn sum_at(b: &mut Builder) -> Lemma {
    let d = ("gdvaddbr.1", "|- ( ph -> D C_ RR )");
    let f = ("gdvaddbr.2", "|- ( ph -> F : D --> RR )");
    let g = ("gdvaddbr.3", "|- ( ph -> G : D --> RR )");
    let df = ("gdvaddbr.4", "|- ( ph -> C e. dom ( RR _D F ) )");
    let dg = ("gdvaddbr.5", "|- ( ph -> C e. dom ( RR _D G ) )");
    let statement = "|- ( ph -> C ( RR _D ( F oF + G ) ) \
                     ( ( ( RR _D F ) ` C ) + ( ( RR _D G ) ` C ) ) )";
    let all = [d, f, g, df, dg];
    hypotheses(b, &all);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        // At a point of its domain, a derivative relates it to its value.
        let related = |name: &str, there: &str| {
            let r = format!("( RR _D {name} )");
            let at = format!("C {r} ( {r} ` C )");
            b.ap(
                "sylib",
                &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("C e. dom {r}")),
                "ch" => b.wff(&at)},
                &[
                    &b.step(there),
                    &b.ap(
                        "ax-mp",
                        &binds! {"ph" => b.wff(&format!("Fun {r}")),
                        "ps" => b.wff(&format!("( C e. dom {r} <-> {at} )"))},
                        &[
                            &derivative_function(b, name),
                            &b.ap(
                                "funfvbrb",
                                &binds! {"F" => b.class(&r), "A" => b.class("C")},
                                &[],
                            ),
                        ],
                    ),
                ],
            )
        };
        b.ap(
            "dvaddbr",
            &binds! {"ph" => ph.clone(), "F" => b.class("F"), "X" => b.class("D"),
            "G" => b.class("G"), "Y" => b.class("D"), "S" => b.class("RR"),
            "C" => b.class("C"), "K" => b.class("( ( RR _D F ) ` C )"),
            "L" => b.class("( ( RR _D G ) ` C )"), "J" => b.class(K)},
            &[
                &into_complex(b, "F", "D", &b.step(f.0)),
                &b.step(d.0),
                &into_complex(b, "G", "D", &b.step(g.0)),
                &b.step(d.0),
                &real_complex(b),
                &related("F", df.0),
                &related("G", dg.0),
                &b.ap("eqid", &binds! {"A" => b.class(K)}, &[]),
            ],
        )
    };
    lemma(b, "gdvaddbr", statement, &all, proof)
}

/// What `gdvadd` and `gdvaddv` ask, for `thm:stdlib/calculus/derivative-sum`.
const SUM_RULE: [&str; 7] = [
    "|- ( ph -> D C_ RR )",
    "|- ( ph -> H : D --> RR )",
    "|- ( ph -> F : D --> RR )",
    "|- ( ph -> G : D --> RR )",
    "|- ( ph -> A. x e. D ( H ` x ) = ( ( F ` x ) + ( G ` x ) ) )",
    "|- ( ph -> U C_ dom ( RR _D F ) )",
    "|- ( ph -> U C_ dom ( RR _D G ) )",
];

const SLOPES: &str = "( ( ( RR _D F ) ` x ) + ( ( RR _D G ) ` x ) )";

/// ( ( ph /\ x e. U ) -> x ( RR _D H ) ( F′(x) + G′(x) ) ): `gdvaddbr` at
/// the point, carried from the pointwise sum to H by `gdvaddof`.
fn sum_related(b: &Builder, said: &[(&str, &'static str)]) -> Proof {
    let at = "( ph /\\ x e. U )";
    let lift = |i: usize| {
        let what = said[i].1.trim_start_matches("|- ( ph -> ");
        at_point(b, &what[..what.len() - 2], &b.step(said[i].0))
    };
    let within = |i: usize, name: &str| {
        b.ap(
            "sseldd",
            &binds! {"ph" => b.wff(at), "A" => b.class("U"),
            "B" => b.class(&format!("dom ( RR _D {name} )")), "C" => b.class("x")},
            &[
                &lift(i),
                &b.ap(
                    "simpr",
                    &binds! {"ph" => b.wff("ph"), "ps" => b.wff("x e. U")},
                    &[],
                ),
            ],
        )
    };
    let rule: Vec<Proof> = said[..5].iter().map(|(l, _)| b.step(l)).collect();
    let pointwise = b.ap(
        "gdvaddof",
        &binds! {"ph" => b.wff("ph"), "D" => b.class("D"), "H" => b.class("H"),
        "F" => b.class("F"), "G" => b.class("G"), "x" => b.float("x")},
        &rule.iter().collect::<Vec<_>>(),
    );
    let of_parts = b.ap(
        "gdvaddbr",
        &binds! {"ph" => b.wff(at), "D" => b.class("D"), "F" => b.class("F"),
        "G" => b.class("G"), "C" => b.class("x")},
        &[
            &lift(0),
            &lift(2),
            &lift(3),
            &within(5, "F"),
            &within(6, "G"),
        ],
    );
    let same = b.ap(
        "breqd",
        &binds! {"ph" => b.wff(at), "A" => b.class("( RR _D H )"),
        "B" => b.class(&format!("( RR _D {ADDED} )")), "C" => b.class("x"),
        "D" => b.class(SLOPES)},
        &[&b.ap(
            "oveq2d",
            &binds! {"ph" => b.wff(at), "A" => b.class("H"), "B" => b.class(ADDED),
            "C" => b.class("RR"), "F" => b.class("_D")},
            &[&at_point(b, &format!("H = {ADDED}"), &pointwise)],
        )],
    );
    b.ap(
        "mpbird",
        &binds! {"ph" => b.wff(at), "ps" => b.wff(&format!("x ( RR _D H ) {SLOPES}")),
        "ch" => b.wff(&format!("x ( RR _D {ADDED} ) {SLOPES}"))},
        &[&of_parts, &same],
    )
}

/// `gdvadd`: a sum is differentiable wherever both its parts are.
fn sum_domain(b: &mut Builder) -> Lemma {
    let hyps = labelled("gdvadd", &SUM_RULE);
    let said = pairs(&hyps);
    let statement = "|- ( ph -> U C_ dom ( RR _D H ) )";
    hypotheses(b, &said);
    let proof = {
        let b: &Builder = b;
        let at = "( ph /\\ x e. U )";
        let related = sum_related(b, &said);
        let inside = b.ap(
            "syl2anc",
            &binds! {"ph" => b.wff(at), "ps" => b.wff("Rel ( RR _D H )"),
            "ch" => b.wff(&format!("x ( RR _D H ) {SLOPES}")),
            "th" => b.wff("x e. dom ( RR _D H )")},
            &[
                &b.ap(
                    "a1i",
                    &binds! {"ph" => b.wff("Rel ( RR _D H )"), "ps" => b.wff(at)},
                    &[&b.ap(
                        "reldv",
                        &binds! {"S" => b.class("RR"), "F" => b.class("H")},
                        &[],
                    )],
                ),
                &related,
                &b.ap(
                    "releldm",
                    &binds! {"R" => b.class("( RR _D H )"), "A" => b.class("x"),
                    "B" => b.class(SLOPES)},
                    &[],
                ),
            ],
        );
        b.ap(
            "ssrdv",
            &binds! {"ph" => b.wff("ph"), "A" => b.class("U"),
            "B" => b.class("dom ( RR _D H )"), "x" => b.float("x")},
            &[&b.ap(
                "ex",
                &binds! {"ph" => b.wff("ph"), "ps" => b.wff("x e. U"),
                "ch" => b.wff("x e. dom ( RR _D H )")},
                &[&inside],
            )],
        )
    };
    lemma(b, "gdvadd", statement, &said, proof)
}

/// `gdvaddv`: the derivative of a sum is the sum of the derivatives.
fn sum_values(b: &mut Builder) -> Lemma {
    let hyps = labelled("gdvaddv", &SUM_RULE);
    let said = pairs(&hyps);
    let statement = format!("|- ( ph -> A. x e. U ( ( RR _D H ) ` x ) = {SLOPES} )");
    hypotheses(b, &said);
    let proof = {
        let b: &Builder = b;
        let at = "( ph /\\ x e. U )";
        let relation = format!("x ( RR _D H ) {SLOPES}");
        let value = format!("( ( RR _D H ) ` x ) = {SLOPES}");
        let at_x = b.ap(
            "syl2anc",
            &binds! {"ph" => b.wff(at), "ps" => b.wff("Fun ( RR _D H )"),
            "ch" => b.wff(&relation), "th" => b.wff(&value)},
            &[
                &b.ap(
                    "a1i",
                    &binds! {"ph" => b.wff("Fun ( RR _D H )"), "ps" => b.wff(at)},
                    &[&derivative_function(b, "H")],
                ),
                &sum_related(b, &said),
                &b.ap(
                    "imp",
                    &binds! {"ph" => b.wff("Fun ( RR _D H )"), "ps" => b.wff(&relation),
                    "ch" => b.wff(&value)},
                    &[&b.ap(
                        "funbrfv",
                        &binds! {"F" => b.class("( RR _D H )"), "A" => b.class("x"),
                        "B" => b.class(SLOPES)},
                        &[],
                    )],
                ),
            ],
        );
        b.ap(
            "ralrimiva",
            &binds! {"ph" => b.wff("ph"), "ps" => b.wff(&value), "x" => b.float("x"),
            "A" => b.class("U")},
            &[&at_x],
        )
    };
    lemma(b, "gdvaddv", &statement, &said, proof)
}

/// What `gdvlinres`, `gdvlin` and `gdvlinv` ask, for
/// `thm:stdlib/calculus/derivative-linear`: a line on D, and an open U
/// inside D.
const LINE_RULE: [&str; 6] = [
    "|- ( ph -> D C_ RR )",
    "|- ( ph -> U C_ D )",
    "|- ( ph -> U e. ( topGen ` ran (,) ) )",
    "|- ( ph -> M e. RR )",
    "|- ( ph -> G : D --> RR )",
    "|- ( ph -> A. x e. D ( G ` x ) = ( M x. x ) )",
];

/// `gdvlinres`: on an open set inside its domain, a line's derivative is
/// its slope.
fn line_restricted(b: &mut Builder) -> Lemma {
    let hyps = labelled("gdvlinres", &LINE_RULE);
    let said = pairs(&hyps);
    let statement = "|- ( ph -> ( ( RR _D G ) |` U ) = ( x e. U |-> M ) )";
    hypotheses(b, &said);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let x = b.float("x");
        let at = "( ph /\\ x e. U )";
        let (d, u_in_d, open, m, g, rule) = (
            b.step(said[0].0),
            b.step(said[1].0),
            b.step(said[2].0),
            b.step(said[3].0),
            b.step(said[4].0),
            b.step(said[5].0),
        );
        let u_real = b.ap(
            "sstrd",
            &binds! {"ph" => ph.clone(), "A" => b.class("U"), "B" => b.class("D"),
            "C" => b.class("RR")},
            &[&u_in_d, &d],
        );
        // The derivative of the restriction is the derivative restricted to
        // the interior of U, which is U.
        let left = "( RR C_ CC /\\ G : D --> CC )";
        let right = "( D C_ RR /\\ U C_ RR )";
        let both = b.ap(
            "jca",
            &binds! {"ph" => ph.clone(), "ps" => b.wff(left), "ch" => b.wff(right)},
            &[
                &b.ap(
                    "jca",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff("RR C_ CC"),
                    "ch" => b.wff("G : D --> CC")},
                    &[&real_complex(b), &into_complex(b, "G", "D", &g)],
                ),
                &b.ap(
                    "jca",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff("D C_ RR"),
                    "ch" => b.wff("U C_ RR")},
                    &[&d, &u_real],
                ),
            ],
        );
        let interior = format!("( ( int ` {T} ) ` U )");
        let of_part = "( RR _D ( G |` U ) )";
        let by_interior = format!("( ( RR _D G ) |` {interior} )");
        let restricted = "( ( RR _D G ) |` U )";
        let res = b.ap(
            "syl",
            &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("( {left} /\\ {right} )")),
            "ch" => b.wff(&format!("{of_part} = {by_interior}"))},
            &[
                &both,
                &b.ap(
                    "dvres",
                    &binds! {"S" => b.class("RR"), "F" => b.class("G"), "A" => b.class("D"),
                    "B" => b.class("U"), "K" => b.class(K), "T" => b.class(T)},
                    &[&b.ap("eqid", &binds! {"A" => b.class(K)}, &[]), &real_topology(b)],
                ),
            ],
        );
        let open_interior = b.ap(
            "syl2anc",
            &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{T} e. Top")),
            "ch" => b.wff(&format!("U e. {T}")), "th" => b.wff(&format!("{interior} = U"))},
            &[
                &b.ap(
                    "a1i",
                    &binds! {"ph" => b.wff(&format!("{T} e. Top")), "ps" => ph.clone()},
                    &[&b.step("retop")],
                ),
                &open,
                &b.ap(
                    "isopn3i",
                    &binds! {"J" => b.class(T), "S" => b.class("U")},
                    &[],
                ),
            ],
        );
        let to_restricted = b.ap(
            "eqtrd",
            &binds! {"ph" => ph.clone(), "A" => b.class(of_part),
            "B" => b.class(&by_interior), "C" => b.class(restricted)},
            &[
                &res,
                &b.ap(
                    "reseq2d",
                    &binds! {"ph" => ph.clone(), "A" => b.class(&interior), "B" => b.class("U"),
                    "C" => b.class("( RR _D G )")},
                    &[&open_interior],
                ),
            ],
        );
        // The restriction is the line on U.
        let on_d = "( x e. D |-> ( M x. x ) )";
        let on_u = "( x e. U |-> ( M x. x ) )";
        let line_on_u = b.ap(
            "eqtrd",
            &binds! {"ph" => ph.clone(), "A" => b.class("( G |` U )"),
            "B" => b.class(&format!("( {on_d} |` U )")), "C" => b.class(on_u)},
            &[
                &b.ap(
                    "reseq1d",
                    &binds! {"ph" => ph.clone(), "A" => b.class("G"), "B" => b.class(on_d),
                    "C" => b.class("U")},
                    &[&as_rule(b, "G", &g, &rule, "( M x. x )")],
                ),
                &b.ap(
                    "syl",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff("U C_ D"),
                    "ch" => b.wff(&format!("( {on_d} |` U ) = {on_u}"))},
                    &[
                        &u_in_d,
                        &b.ap(
                            "resmpt",
                            &binds! {"A" => b.class("D"), "B" => b.class("U"),
                            "C" => b.class("( M x. x )"), "x" => x.clone()},
                            &[],
                        ),
                    ],
                ),
            ],
        );
        // The identity has derivative 1 on ℝ, and so on U, which is open;
        // the line M·x has M·1.
        let at_real = "( ph /\\ x e. RR )";
        let one_at = |ctx: &str| {
            b.ap(
                "a1i",
                &binds! {"ph" => b.wff("1 e. CC"), "ps" => b.wff(ctx)},
                &[&b.step("ax-1cn")],
            )
        };
        let identity = b.ap(
            "dvmptid",
            &binds! {"ph" => ph.clone(), "S" => b.class("RR"), "x" => x.clone()},
            &[&over_reals(b, "ph")],
        );
        let on_open = b.ap(
            "dvmptres",
            &binds! {"ph" => ph.clone(), "S" => b.class("RR"), "X" => b.class("RR"),
            "Y" => b.class("U"), "A" => b.class("x"), "B" => b.class("1"),
            "V" => b.class("CC"), "J" => b.class(T), "K" => b.class(K), "x" => x.clone()},
            &[
                &over_reals(b, "ph"),
                &b.ap(
                    "recnd",
                    &binds! {"ph" => b.wff(at_real), "A" => b.class("x")},
                    &[&b.ap(
                        "simpr",
                        &binds! {"ph" => ph.clone(), "ps" => b.wff("x e. RR")},
                        &[],
                    )],
                ),
                &one_at(at_real),
                &identity,
                &u_real,
                &real_topology(b),
                &b.ap("eqid", &binds! {"A" => b.class(K)}, &[]),
                &open,
            ],
        );
        let x_complex = b.ap(
            "recnd",
            &binds! {"ph" => b.wff(at), "A" => b.class("x")},
            &[&b.ap(
                "sseldd",
                &binds! {"ph" => b.wff(at), "A" => b.class("U"), "B" => b.class("RR"),
                "C" => b.class("x")},
                &[
                    &at_point(b, "U C_ RR", &u_real),
                    &b.ap(
                        "simpr",
                        &binds! {"ph" => ph.clone(), "ps" => b.wff("x e. U")},
                        &[],
                    ),
                ],
            )],
        );
        let m_complex = b.ap(
            "recnd",
            &binds! {"ph" => ph.clone(), "A" => b.class("M")},
            &[&m],
        );
        let scaled = b.ap(
            "dvmptcmul",
            &binds! {"ph" => ph.clone(), "S" => b.class("RR"), "X" => b.class("U"),
            "A" => b.class("x"), "B" => b.class("1"), "V" => b.class("CC"),
            "C" => b.class("M"), "x" => x.clone()},
            &[
                &over_reals(b, "ph"),
                &x_complex,
                &one_at(at),
                &on_open,
                &m_complex,
            ],
        );
        let slope = b.ap(
            "mpteq2dva",
            &binds! {"ph" => ph.clone(), "x" => x, "A" => b.class("U"),
            "B" => b.class("( M x. 1 )"), "C" => b.class("M")},
            &[&b.ap(
                "mulridd",
                &binds! {"ph" => b.wff(at), "A" => b.class("M")},
                &[&at_point(b, "M e. CC", &m_complex)],
            )],
        );
        let of_line = format!("( RR _D {on_u} )");
        let times_one = "( x e. U |-> ( M x. 1 ) )";
        let constant = "( x e. U |-> M )";
        let chain = [
            (
                restricted.to_string(),
                of_part.to_string(),
                b.ap(
                    "eqcomd",
                    &binds! {"ph" => ph.clone(), "A" => b.class(of_part),
                    "B" => b.class(restricted)},
                    &[&to_restricted],
                ),
            ),
            (
                of_part.to_string(),
                of_line.clone(),
                b.ap(
                    "oveq2d",
                    &binds! {"ph" => ph.clone(), "A" => b.class("( G |` U )"),
                    "B" => b.class(on_u), "C" => b.class("RR"), "F" => b.class("_D")},
                    &[&line_on_u],
                ),
            ),
            (of_line, times_one.to_string(), scaled),
            (times_one.to_string(), constant.to_string(), slope),
        ];
        let mut proof = chain[0].2.clone();
        for (from, to, step) in &chain[1..] {
            proof = b.ap(
                "eqtrd",
                &binds! {"ph" => ph.clone(), "A" => b.class(restricted),
                "B" => b.class(from), "C" => b.class(to)},
                &[&proof, step],
            );
        }
        proof
    };
    lemma(b, "gdvlinres", statement, &said, proof)
}

/// ( ( ph /\ x e. U ) -> M e. RR ), from the rule's slope hypothesis.
fn slope_real(b: &Builder, said: &[(&str, &'static str)]) -> Proof {
    at_point(b, "M e. RR", &b.step(said[3].0))
}

/// ( ph -> ( ( RR _D G ) |` U ) = ( x e. U |-> M ) ), by `gdvlinres`.
fn line_as_map(b: &Builder, said: &[(&str, &'static str)]) -> Proof {
    let rule: Vec<Proof> = said.iter().map(|(l, _)| b.step(l)).collect();
    b.ap(
        "gdvlinres",
        &binds! {"ph" => b.wff("ph"), "D" => b.class("D"), "U" => b.class("U"),
        "M" => b.class("M"), "G" => b.class("G"), "x" => b.float("x")},
        &rule.iter().collect::<Vec<_>>(),
    )
}

/// `gdvlin`: a line is differentiable on an open set inside its domain.
fn line_domain(b: &mut Builder) -> Lemma {
    let hyps = labelled("gdvlin", &LINE_RULE);
    let said = pairs(&hyps);
    let statement = "|- ( ph -> U C_ dom ( RR _D G ) )";
    hypotheses(b, &said);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let restricted = "( ( RR _D G ) |` U )";
        let on_part = b.ap(
            "gdvdm",
            &binds! {"ph" => ph.clone(), "D" => b.class(restricted), "x" => b.float("x"),
            "I" => b.class("U"), "E" => b.class("M"), "V" => b.class("RR")},
            &[&line_as_map(b, &said), &slope_real(b, &said)],
        );
        let part_within = b.ap(
            "eqsstrd",
            &binds! {"ph" => ph.clone(), "A" => b.class(&format!("dom {restricted}")),
            "B" => b.class("( U i^i dom ( RR _D G ) )"), "C" => b.class("dom ( RR _D G )")},
            &[
                &b.ap(
                    "a1i",
                    &binds! {"ph" => b.wff(&format!(
                        "dom {restricted} = ( U i^i dom ( RR _D G ) )"
                    )), "ps" => ph.clone()},
                    &[&b.ap(
                        "dmres",
                        &binds! {"A" => b.class("( RR _D G )"), "B" => b.class("U")},
                        &[],
                    )],
                ),
                &b.ap(
                    "a1i",
                    &binds! {"ph" => b.wff("( U i^i dom ( RR _D G ) ) C_ dom ( RR _D G )"),
                    "ps" => ph.clone()},
                    &[&b.ap(
                        "inss2",
                        &binds! {"A" => b.class("U"), "B" => b.class("dom ( RR _D G )")},
                        &[],
                    )],
                ),
            ],
        );
        b.ap(
            "sstrd",
            &binds! {"ph" => ph, "A" => b.class("U"),
            "B" => b.class(&format!("dom {restricted}")), "C" => b.class("dom ( RR _D G )")},
            &[&on_part, &part_within],
        )
    };
    lemma(b, "gdvlin", statement, &said, proof)
}

/// `gdvlinv`: on an open set inside its domain, a line's derivative at each
/// point is its slope.
fn line_values(b: &mut Builder) -> Lemma {
    let hyps = labelled("gdvlinv", &LINE_RULE);
    let said = pairs(&hyps);
    let statement = "|- ( ph -> A. x e. U ( ( RR _D G ) ` x ) = M )";
    hypotheses(b, &said);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let x = b.float("x");
        let at = "( ph /\\ x e. U )";
        let restricted = "( ( RR _D G ) |` U )";
        let on_part = b.ap(
            "gdvval",
            &binds! {"ph" => ph.clone(), "D" => b.class(restricted), "x" => x.clone(),
            "I" => b.class("U"), "E" => b.class("M"), "V" => b.class("RR")},
            &[&line_as_map(b, &said), &slope_real(b, &said)],
        );
        let part_value = format!("( {restricted} ` x ) = M");
        let there = b.ap(
            "r19.21bi",
            &binds! {"ph" => ph.clone(), "ps" => b.wff(&part_value), "x" => x.clone(),
            "A" => b.class("U")},
            &[&on_part],
        );
        let same = b.ap(
            "syl",
            &binds! {"ph" => b.wff(at), "ps" => b.wff("x e. U"),
            "ch" => b.wff(&format!("( {restricted} ` x ) = ( ( RR _D G ) ` x )"))},
            &[
                &b.ap(
                    "simpr",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff("x e. U")},
                    &[],
                ),
                &b.ap(
                    "fvres",
                    &binds! {"A" => b.class("x"), "B" => b.class("U"),
                    "F" => b.class("( RR _D G )")},
                    &[],
                ),
            ],
        );
        let value = b.ap(
            "eqtr3d",
            &binds! {"ph" => b.wff(at), "A" => b.class(&format!("( {restricted} ` x )")),
            "B" => b.class("( ( RR _D G ) ` x )"), "C" => b.class("M")},
            &[&same, &there],
        );
        b.ap(
            "ralrimiva",
            &binds! {"ph" => ph, "ps" => b.wff("( ( RR _D G ) ` x ) = M"), "x" => x,
            "A" => b.class("U")},
            &[&value],
        )
    };
    lemma(b, "gdvlinv", statement, &said, proof)
}

/// ( ph -> f e. ( D -cn-> RR ) ) from its map continuous into ℂ and f's
/// values real: `cncfcdm`, carried to f by its equation with the map.
fn continuous_real(
    b: &Builder,
    f: &str,
    typed: &Proof,
    is_map: &Proof,
    map: &str,
    continuous: &Proof,
) -> Proof {
    let ph = b.wff("ph");
    let map_typed = b.ap(
        "mpbid",
        &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{f} : D --> RR")),
        "ch" => b.wff(&format!("{map} : D --> RR"))},
        &[
            typed,
            &b.ap(
                "feq1d",
                &binds! {"ph" => ph.clone(), "F" => b.class(f), "G" => b.class(map),
                "A" => b.class("D"), "B" => b.class("RR")},
                &[is_map],
            ),
        ],
    );
    let narrowed = b.ap(
        "syl2anc",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("RR C_ CC"),
        "ch" => b.wff(&format!("{map} e. ( D -cn-> CC )")),
        "th" => b.wff(&format!("( {map} e. ( D -cn-> RR ) <-> {map} : D --> RR )"))},
        &[
            &real_complex(b),
            continuous,
            &b.ap(
                "cncfcdm",
                &binds! {"A" => b.class("D"), "B" => b.class("CC"), "C" => b.class("RR"),
                "F" => b.class(map)},
                &[],
            ),
        ],
    );
    let real = b.ap(
        "mpbird",
        &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{map} e. ( D -cn-> RR )")),
        "ch" => b.wff(&format!("{map} : D --> RR"))},
        &[&map_typed, &narrowed],
    );
    b.ap(
        "eqeltrd",
        &binds! {"ph" => ph, "A" => b.class(f), "B" => b.class(map),
        "C" => b.class("( D -cn-> RR )")},
        &[is_map, &real],
    )
}

/// `gcncflin`: for `thm:stdlib/calculus/continuous-linear`.
fn continuous_line(b: &mut Builder) -> Lemma {
    let d = ("gcncflin.1", "|- ( ph -> D C_ RR )");
    let m = ("gcncflin.2", "|- ( ph -> M e. RR )");
    let g = ("gcncflin.3", "|- ( ph -> G : D --> RR )");
    let rule = (
        "gcncflin.4",
        "|- ( ph -> A. x e. D ( G ` x ) = ( M x. x ) )",
    );
    let statement = "|- ( ph -> G e. ( D -cn-> RR ) )";
    let all = [d, m, g, rule];
    hypotheses(b, &all);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let x = b.float("x");
        let map = "( x e. D |-> ( M x. x ) )";
        let is_map = as_rule(b, "G", &b.step(g.0), &b.step(rule.0), "( M x. x )");
        let d_complex = b.ap(
            "sstrd",
            &binds! {"ph" => ph.clone(), "A" => b.class("D"), "B" => b.class("RR"),
            "C" => b.class("CC")},
            &[&b.step(d.0), &real_complex(b)],
        );
        let cc_cc = b.ap(
            "a1i",
            &binds! {"ph" => b.wff("CC C_ CC"), "ps" => ph.clone()},
            &[&b.ap("ssid", &binds! {"A" => b.class("CC")}, &[])],
        );
        let constant = b.ap(
            "syl3anc",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("M e. CC"), "ch" => b.wff("D C_ CC"),
            "th" => b.wff("CC C_ CC"),
            "ta" => b.wff("( x e. D |-> M ) e. ( D -cn-> CC )")},
            &[
                &b.ap(
                    "recnd",
                    &binds! {"ph" => ph.clone(), "A" => b.class("M")},
                    &[&b.step(m.0)],
                ),
                &d_complex,
                &cc_cc,
                &b.ap(
                    "cncfmptc",
                    &binds! {"x" => x.clone(), "A" => b.class("M"), "S" => b.class("D"),
                    "T" => b.class("CC")},
                    &[],
                ),
            ],
        );
        let identity = b.ap(
            "syl2anc",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("D C_ CC"), "ch" => b.wff("CC C_ CC"),
            "th" => b.wff("( x e. D |-> x ) e. ( D -cn-> CC )")},
            &[
                &d_complex,
                &cc_cc,
                &b.ap(
                    "cncfmptid",
                    &binds! {"x" => x.clone(), "S" => b.class("D"), "T" => b.class("CC")},
                    &[],
                ),
            ],
        );
        let product = b.ap(
            "mulcncf",
            &binds! {"ph" => ph.clone(), "x" => x, "X" => b.class("D"),
            "A" => b.class("M"), "B" => b.class("x")},
            &[&constant, &identity],
        );
        continuous_real(b, "G", &b.step(g.0), &is_map, map, &product)
    };
    lemma(b, "gcncflin", statement, &all, proof)
}

/// `gcncfadd`: for `thm:stdlib/calculus/continuous-sum`.
fn continuous_sum(b: &mut Builder) -> Lemma {
    let d = ("gcncfadd.1", "|- ( ph -> D C_ RR )");
    let h = ("gcncfadd.2", "|- ( ph -> H : D --> RR )");
    let f = ("gcncfadd.3", "|- ( ph -> F : D --> RR )");
    let g = ("gcncfadd.4", "|- ( ph -> G : D --> RR )");
    let rule = (
        "gcncfadd.5",
        "|- ( ph -> A. x e. D ( H ` x ) = ( ( F ` x ) + ( G ` x ) ) )",
    );
    let fc = ("gcncfadd.6", "|- ( ph -> F e. ( D -cn-> RR ) )");
    let gc = ("gcncfadd.7", "|- ( ph -> G e. ( D -cn-> RR ) )");
    let statement = "|- ( ph -> H e. ( D -cn-> RR ) )";
    let all = [d, h, f, g, rule, fc, gc];
    hypotheses(b, &all);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let x = b.float("x");
        let map = format!("( x e. D |-> {SUM} )");
        let wider = b.ap(
            "a1i",
            &binds! {"ph" => b.wff("( D -cn-> RR ) C_ ( D -cn-> CC )"), "ps" => ph.clone()},
            &[&b.ap(
                "mp2an",
                &binds! {"ph" => b.wff("RR C_ CC"), "ps" => b.wff("CC C_ CC"),
                "ch" => b.wff("( D -cn-> RR ) C_ ( D -cn-> CC )")},
                &[
                    &b.step("ax-resscn"),
                    &b.ap("ssid", &binds! {"A" => b.class("CC")}, &[]),
                    &b.ap(
                        "cncfss",
                        &binds! {"A" => b.class("D"), "B" => b.class("RR"),
                        "C" => b.class("CC")},
                        &[],
                    ),
                ],
            )],
        );
        // Each part, continuous into ℂ, as the map of its values.
        let part = |name: &str, typed: &str, continuous: &str| {
            let values = format!("( x e. D |-> ( {name} ` x ) )");
            let as_values = b.ap(
                "sylib",
                &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{name} Fn D")),
                "ch" => b.wff(&format!("{name} = {values}"))},
                &[
                    &b.ap(
                        "ffnd",
                        &binds! {"ph" => ph.clone(), "F" => b.class(name), "A" => b.class("D"),
                        "B" => b.class("RR")},
                        &[&b.step(typed)],
                    ),
                    &b.ap(
                        "dffn5",
                        &binds! {"x" => x.clone(), "A" => b.class("D"), "F" => b.class(name)},
                        &[],
                    ),
                ],
            );
            let into_cc = b.ap(
                "sseldd",
                &binds! {"ph" => ph.clone(), "A" => b.class("( D -cn-> RR )"),
                "B" => b.class("( D -cn-> CC )"), "C" => b.class(name)},
                &[&wider, &b.step(continuous)],
            );
            b.ap(
                "eqeltrrd",
                &binds! {"ph" => ph.clone(), "A" => b.class(name), "B" => b.class(&values),
                "C" => b.class("( D -cn-> CC )")},
                &[&as_values, &into_cc],
            )
        };
        let added = b.ap(
            "addcncf",
            &binds! {"ph" => ph.clone(), "x" => x.clone(), "X" => b.class("D"),
            "A" => b.class("( F ` x )"), "B" => b.class("( G ` x )")},
            &[&part("F", f.0, fc.0), &part("G", g.0, gc.0)],
        );
        let is_map = as_rule(b, "H", &b.step(h.0), &b.step(rule.0), SUM);
        continuous_real(b, "H", &b.step(h.0), &is_map, &map, &added)
    };
    lemma(b, "gcncfadd", statement, &all, proof)
}

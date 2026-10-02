//! Calculus, for `proved.mm`.
//!
//! The mean value theorem asks what a textbook calls the sum rules: a sum of
//! continuous functions is continuous, a line is, and the derivative of a sum
//! is the sum of the derivatives, of a line its slope. set.mm says each of a
//! map written out, `( x e. X |-> A )`, and the page says it of functions
//! named apart from their values, F with F(x) = f(x) + g(x) for every x.
//! Each lemma here is the page's form: the function is its map (`dffn5`),
//! the map's values are rewritten by what the page says of them
//! (`mpteq2dva`), and set.mm's rule is applied to the map.
//!
//! A function on [a, b] is differentiable on (a, b) at most, since a
//! derivative is taken only where a neighbourhood lies in the domain
//! (`dvbssntr`, `iccntr`). So its derivative is that of its restriction to
//! (a, b) (`dvres`, `ioontr`), which is where set.mm's rules for maps apply
//! (`gdvloc`, `gdvmpt`). Derivatives are into ℂ in set.mm, and a real
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
$d x V $.

";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![
        domain(b),
        values(b),
        restricted(b),
        derivative_type(b),
        derivative_real(b),
        derivative_map(b),
        derivative_line(b),
        line_domain(b),
        line_values(b),
        derivative_sum(b),
        sum_domain(b),
        sum_values(b),
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

/// `gdvdm`: a map on I is defined exactly on I.
fn domain(b: &mut Builder) -> Lemma {
    let is_map = ("gdvdm.1", "|- ( ph -> D = ( x e. I |-> E ) )");
    let a_set = ("gdvdm.2", "|- ( ( ph /\\ x e. I ) -> E e. V )");
    let statement = "|- ( ph -> dom D = I )";
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
        b.ap(
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

/// One sentence of what a derivative rule concludes, read off the lemma
/// giving the derivative as a map: its domain (`gdvdm`) or its values
/// (`gdvval`). `hyps` are the rule's, the map lemma's alike.
#[allow(clippy::too_many_arguments)]
fn read_off(
    b: &mut Builder,
    label: &str,
    hyps: &[(&str, &str)],
    map_lemma: &str,
    map_binds: &[(&str, &str)],
    whole: &str,
    rule: &str,
    set: &str,
    a_set: fn(&Builder, &str) -> Proof,
    values: bool,
) -> Lemma {
    let statement = if values {
        format!("|- ( ph -> A. x e. {OPEN} ( {whole} ` x ) = {rule} )")
    } else {
        format!("|- ( ph -> dom {whole} = {OPEN} )")
    };
    let renamed: Vec<(String, String)> = hyps
        .iter()
        .enumerate()
        .map(|(i, (_, s))| (format!("{label}.{}", i + 1), s.to_string()))
        .collect();
    let said: Vec<(&str, &str)> = renamed
        .iter()
        .map(|(l, s)| (l.as_str(), s.as_str()))
        .collect();
    hypotheses(b, &said);
    let proof = {
        let b: &Builder = b;
        let x = b.float("x");
        let mut binds = binds! {"ph" => b.wff("ph"), "x" => x.clone()};
        for (var, term) in map_binds {
            binds.insert(var.to_string(), b.class(term));
        }
        let steps: Vec<Proof> = said.iter().map(|(l, _)| b.step(l)).collect();
        let as_map = b.ap(map_lemma, &binds, &steps.iter().collect::<Vec<_>>());
        b.ap(
            if values { "gdvval" } else { "gdvdm" },
            &binds! {"ph" => b.wff("ph"), "D" => b.class(whole), "x" => x,
            "I" => b.class(OPEN), "E" => b.class(rule), "V" => b.class(set)},
            &[&as_map, &a_set(b, label)],
        )
    };
    lemma(b, label, &statement, &said, proof)
}

/// ( ph -> RR C_ CC )
fn real_complex(b: &Builder) -> Proof {
    b.ap(
        "a1i",
        &binds! {"ph" => b.wff("RR C_ CC"), "ps" => b.wff("ph")},
        &[&b.step("ax-resscn")],
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

/// ( ph -> ( A (,) B ) C_ ( A [,] B ) )
fn open_within(b: &Builder, ph: &str) -> Proof {
    b.ap(
        "a1i",
        &binds! {"ph" => b.wff(&format!("{OPEN} C_ {AB}")), "ps" => b.wff(ph)},
        &[&b.ap(
            "ioossicc",
            &binds! {"A" => b.class("A"), "B" => b.class("B")},
            &[],
        )],
    )
}

/// `gdvloc`: a function on [a, b] has the derivative its restriction to
/// (a, b) has.
fn restricted(b: &mut Builder) -> Lemma {
    let a = ("gdvloc.1", "|- ( ph -> A e. RR )");
    let bb = ("gdvloc.2", "|- ( ph -> B e. RR )");
    let f = ("gdvloc.3", "|- ( ph -> F : ( A [,] B ) --> CC )");
    let statement = "|- ( ph -> ( RR _D ( F |` ( A (,) B ) ) ) = ( RR _D F ) )";
    hypotheses(b, &[a, bb, f]);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let tg = real_topology(b);
        let rr_cc = real_complex(b);
        let ab_rr = closed_real(b, a.0, bb.0);
        let open_rr = b.ap(
            "a1i",
            &binds! {"ph" => b.wff(&format!("{OPEN} C_ RR")), "ps" => ph.clone()},
            &[&b.ap(
                "ioossre",
                &binds! {"A" => b.class("A"), "B" => b.class("B")},
                &[],
            )],
        );
        let left = format!("( RR C_ CC /\\ F : {AB} --> CC )");
        let right = format!("( {AB} C_ RR /\\ {OPEN} C_ RR )");
        let both = b.ap(
            "jca",
            &binds! {"ph" => ph.clone(), "ps" => b.wff(&left), "ch" => b.wff(&right)},
            &[
                &b.ap(
                    "jca",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff("RR C_ CC"),
                    "ch" => b.wff(&format!("F : {AB} --> CC"))},
                    &[&rr_cc, &b.step(f.0)],
                ),
                &b.ap(
                    "jca",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("{AB} C_ RR")),
                    "ch" => b.wff(&format!("{OPEN} C_ RR"))},
                    &[&ab_rr, &open_rr],
                ),
            ],
        );
        let inside = format!("( ( int ` {T} ) ` {OPEN} )");
        let restricted = format!("( RR _D ( F |` {OPEN} ) )");
        let by_inside = format!("( ( RR _D F ) |` {inside} )");
        let by_open = format!("( ( RR _D F ) |` {OPEN} )");
        let res = b.ap(
            "syl",
            &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("( {left} /\\ {right} )")),
            "ch" => b.wff(&format!("{restricted} = {by_inside}"))},
            &[
                &both,
                &b.ap(
                    "dvres",
                    &binds! {"S" => b.class("RR"), "F" => b.class("F"), "A" => b.class(AB),
                    "B" => b.class(OPEN), "K" => b.class(K), "T" => b.class(T)},
                    &[&b.ap("eqid", &binds! {"A" => b.class(K)}, &[]), &tg],
                ),
            ],
        );
        let interior = b.ap(
            "reseq2d",
            &binds! {"ph" => ph.clone(), "A" => b.class(&inside), "B" => b.class(OPEN),
            "C" => b.class("( RR _D F )")},
            &[&b.ap(
                "a1i",
                &binds! {"ph" => b.wff(&format!("{inside} = {OPEN}")), "ps" => ph.clone()},
                &[&b.ap(
                    "ioontr",
                    &binds! {"A" => b.class("A"), "B" => b.class("B")},
                    &[],
                )],
            )],
        );
        let to_open = b.ap(
            "eqtrd",
            &binds! {"ph" => ph.clone(), "A" => b.class(&restricted),
            "B" => b.class(&by_inside), "C" => b.class(&by_open)},
            &[&res, &interior],
        );
        let rel = b.ap(
            "a1i",
            &binds! {"ph" => b.wff("Rel ( RR _D F )"), "ps" => ph.clone()},
            &[&b.ap(
                "reldv",
                &binds! {"S" => b.class("RR"), "F" => b.class("F")},
                &[],
            )],
        );
        let closed_inside = format!("( ( int ` {T} ) ` {AB} )");
        let within = b.ap(
            "dvbssntr",
            &binds! {"ph" => ph.clone(), "S" => b.class("RR"), "F" => b.class("F"),
            "A" => b.class(AB), "J" => b.class(T), "K" => b.class(K)},
            &[
                &rr_cc,
                &b.step(f.0),
                &ab_rr,
                &tg,
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
        let domain = b.ap(
            "sseqtrd",
            &binds! {"ph" => ph.clone(), "A" => b.class("dom ( RR _D F )"),
            "B" => b.class(&closed_inside), "C" => b.class(OPEN)},
            &[&within, &interior_closed],
        );
        let whole = b.ap(
            "syl2anc",
            &binds! {"ph" => ph.clone(), "ps" => b.wff("Rel ( RR _D F )"),
            "ch" => b.wff(&format!("dom ( RR _D F ) C_ {OPEN}")),
            "th" => b.wff(&format!("{by_open} = ( RR _D F )"))},
            &[
                &rel,
                &domain,
                &b.ap(
                    "relssres",
                    &binds! {"A" => b.class("( RR _D F )"), "B" => b.class(OPEN)},
                    &[],
                ),
            ],
        );
        b.ap(
            "eqtrd",
            &binds! {"ph" => ph, "A" => b.class(&restricted), "B" => b.class(&by_open),
            "C" => b.class("( RR _D F )")},
            &[&to_open, &whole],
        )
    };
    lemma(b, "gdvloc", statement, &[a, bb, f], proof)
}

/// The four hypotheses `gdvf`, `gdvre` and `gdvmpt` share, under a label of
/// each lemma's own.
fn differentiable(label: &str) -> [(String, &'static str); 4] {
    [
        (format!("{label}.1"), "|- ( ph -> A e. RR )"),
        (format!("{label}.2"), "|- ( ph -> B e. RR )"),
        (format!("{label}.3"), "|- ( ph -> F : ( A [,] B ) --> RR )"),
        (
            format!("{label}.4"),
            "|- ( ph -> dom ( RR _D F ) = ( A (,) B ) )",
        ),
    ]
}

fn pairs<'a>(hyps: &'a [(String, &'static str)]) -> Vec<(&'a str, &'static str)> {
    hyps.iter().map(|(l, s)| (l.as_str(), *s)).collect()
}

/// `gdvf`: a real function differentiable on (a, b) has a real derivative
/// there.
fn derivative_type(b: &mut Builder) -> Lemma {
    let hyps = differentiable("gdvf");
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
        let moved = b.ap(
            "feq2d",
            &binds! {"ph" => ph.clone(), "A" => b.class("dom ( RR _D F )"),
            "B" => b.class(OPEN), "C" => b.class("RR"), "F" => b.class("( RR _D F )")},
            &[&b.step(said[3].0)],
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
    let hyps = differentiable("gdvre");
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

/// `gdvmpt`: the derivative of a function differentiable on (a, b), as a
/// map of its values there.
fn derivative_map(b: &mut Builder) -> Lemma {
    let hyps = differentiable("gdvmpt");
    let said = pairs(&hyps);
    let statement = "|- ( ph -> ( RR _D ( x e. ( A (,) B ) |-> ( F ` x ) ) ) = \
                     ( x e. ( A (,) B ) |-> ( ( RR _D F ) ` x ) ) )";
    hypotheses(b, &said);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let x = b.float("x");
        let values = format!("( x e. {OPEN} |-> ( F ` x ) )");
        let slopes = format!("( x e. {OPEN} |-> ( ( RR _D F ) ` x ) )");
        let restricted = format!("( F |` {OPEN} )");
        let into_cc = b.ap(
            "fssd",
            &binds! {"ph" => ph.clone(), "F" => b.class("F"), "A" => b.class(AB),
            "B" => b.class("RR"), "C" => b.class("CC")},
            &[&b.step(said[2].0), &real_complex(b)],
        );
        let as_values = b.ap(
            "feqresmpt",
            &binds! {"ph" => ph.clone(), "F" => b.class("F"), "A" => b.class(AB),
            "B" => b.class("RR"), "C" => b.class(OPEN), "x" => x.clone()},
            &[&b.step(said[2].0), &open_within(b, "ph")],
        );
        let local = b.ap(
            "gdvloc",
            &binds! {"ph" => ph.clone(), "A" => b.class("A"), "B" => b.class("B"),
            "F" => b.class("F")},
            &[&b.step(said[0].0), &b.step(said[1].0), &into_cc],
        );
        let same = b.ap(
            "oveq2d",
            &binds! {"ph" => ph.clone(), "A" => b.class(&values), "B" => b.class(&restricted),
            "C" => b.class("RR"), "F" => b.class("_D")},
            &[&b.ap(
                "eqcomd",
                &binds! {"ph" => ph.clone(), "A" => b.class(&restricted),
                "B" => b.class(&values)},
                &[&as_values],
            )],
        );
        let to_f = b.ap(
            "eqtrd",
            &binds! {"ph" => ph.clone(), "A" => b.class(&format!("( RR _D {values} )")),
            "B" => b.class(&format!("( RR _D {restricted} )")),
            "C" => b.class("( RR _D F )")},
            &[&same, &local],
        );
        let typed = b.ap(
            "gdvf",
            &binds! {"ph" => ph.clone(), "A" => b.class("A"), "B" => b.class("B"),
            "F" => b.class("F")},
            &[
                &b.step(said[0].0),
                &b.step(said[1].0),
                &b.step(said[2].0),
                &b.step(said[3].0),
            ],
        );
        let on = b.ap(
            "ffnd",
            &binds! {"ph" => ph.clone(), "F" => b.class("( RR _D F )"), "A" => b.class(OPEN),
            "B" => b.class("RR")},
            &[&typed],
        );
        let as_map = b.ap(
            "sylib",
            &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("( RR _D F ) Fn {OPEN}")),
            "ch" => b.wff(&format!("( RR _D F ) = {slopes}"))},
            &[
                &on,
                &b.ap(
                    "dffn5",
                    &binds! {"x" => x, "A" => b.class(OPEN), "F" => b.class("( RR _D F )")},
                    &[],
                ),
            ],
        );
        b.ap(
            "eqtrd",
            &binds! {"ph" => ph, "A" => b.class(&format!("( RR _D {values} )")),
            "B" => b.class("( RR _D F )"), "C" => b.class(&slopes)},
            &[&to_f, &as_map],
        )
    };
    lemma(b, "gdvmpt", statement, &said, proof)
}

/// ( ph -> ( F |` ( A (,) B ) ) = ( x e. ( A (,) B ) |-> rule ) ), for F on
/// [a, b] whose value at every x there is the rule: `feqresmpt`, then the
/// values rewritten on the smaller interval.
fn restricted_to_rule(
    b: &Builder,
    f: &str,
    typed: &Proof,
    every: &Proof,
    rule: &str,
) -> Proof {
    let ph = b.wff("ph");
    let x = b.float("x");
    let said = format!("( {f} ` x ) = {rule}");
    let values = format!("( x e. {OPEN} |-> ( {f} ` x ) )");
    let ruled = format!("( x e. {OPEN} |-> {rule} )");
    let as_values = b.ap(
        "feqresmpt",
        &binds! {"ph" => ph.clone(), "F" => b.class(f), "A" => b.class(AB),
        "B" => b.class("RR"), "C" => b.class(OPEN), "x" => x.clone()},
        &[typed, &open_within(b, "ph")],
    );
    let narrowed = b.ap(
        "syl",
        &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("A. x e. {AB} {said}")),
        "ch" => b.wff(&format!("A. x e. {OPEN} {said}"))},
        &[
            every,
            &b.ap(
                "ax-mp",
                &binds! {"ph" => b.wff(&format!("{OPEN} C_ {AB}")),
                "ps" => b.wff(&format!("( A. x e. {AB} {said} -> A. x e. {OPEN} {said} )"))},
                &[
                    &b.ap(
                        "ioossicc",
                        &binds! {"A" => b.class("A"), "B" => b.class("B")},
                        &[],
                    ),
                    &b.ap(
                        "ssralv",
                        &binds! {"x" => x.clone(), "A" => b.class(OPEN), "B" => b.class(AB),
                        "ph" => b.wff(&said)},
                        &[],
                    ),
                ],
            ),
        ],
    );
    let rewritten = b.ap(
        "mpteq2dva",
        &binds! {"ph" => ph.clone(), "x" => x.clone(), "A" => b.class(OPEN),
        "B" => b.class(&format!("( {f} ` x )")), "C" => b.class(rule)},
        &[&b.ap(
            "r19.21bi",
            &binds! {"ph" => ph.clone(), "ps" => b.wff(&said), "x" => x,
            "A" => b.class(OPEN)},
            &[&narrowed],
        )],
    );
    b.ap(
        "eqtrd",
        &binds! {"ph" => ph, "A" => b.class(&format!("( {f} |` {OPEN} )")),
        "B" => b.class(&values), "C" => b.class(&ruled)},
        &[&as_values, &rewritten],
    )
}

/// ( ph -> ( RR _D f ) = ( RR _D ( x e. ( A (,) B ) |-> rule ) ) ): the
/// derivative of f on [a, b] is that of its restriction, which is the rule.
fn derivative_of_rule(
    b: &Builder,
    f: &str,
    a: &Proof,
    bb: &Proof,
    typed: &Proof,
    restricted: &Proof,
    rule: &str,
) -> Proof {
    let ph = b.wff("ph");
    let into_cc = b.ap(
        "fssd",
        &binds! {"ph" => ph.clone(), "F" => b.class(f), "A" => b.class(AB),
        "B" => b.class("RR"), "C" => b.class("CC")},
        &[typed, &real_complex(b)],
    );
    let local = b.ap(
        "gdvloc",
        &binds! {"ph" => ph.clone(), "A" => b.class("A"), "B" => b.class("B"),
        "F" => b.class(f)},
        &[a, bb, &into_cc],
    );
    let part = format!("( {f} |` {OPEN} )");
    let ruled = format!("( x e. {OPEN} |-> {rule} )");
    let whole = format!("( RR _D {f} )");
    let of_part = format!("( RR _D {part} )");
    b.ap(
        "eqtrd",
        &binds! {"ph" => ph.clone(), "A" => b.class(&whole), "B" => b.class(&of_part),
        "C" => b.class(&format!("( RR _D {ruled} )"))},
        &[
            &b.ap(
                "eqcomd",
                &binds! {"ph" => ph.clone(), "A" => b.class(&of_part), "B" => b.class(&whole)},
                &[&local],
            ),
            &b.ap(
                "oveq2d",
                &binds! {"ph" => ph, "A" => b.class(&part), "B" => b.class(&ruled),
                "C" => b.class("RR"), "F" => b.class("_D")},
                &[restricted],
            ),
        ],
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

/// `gdvlinmap`: the derivative of a line on [a, b] is its slope on (a, b).
fn derivative_line(b: &mut Builder) -> Lemma {
    let a = ("gdvlinmap.1", LINE[0].1);
    let bb = ("gdvlinmap.2", LINE[1].1);
    let m = ("gdvlinmap.3", LINE[2].1);
    let g = ("gdvlinmap.4", LINE[3].1);
    let rule = ("gdvlinmap.5", LINE[4].1);
    let statement = "|- ( ph -> ( RR _D G ) = ( x e. ( A (,) B ) |-> M ) )";
    let all = [a, bb, m, g, rule];
    hypotheses(b, &all);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let x = b.float("x");
        let at = format!("( ph /\\ x e. {OPEN} )");
        let line = "( M x. x )";
        let restricted =
            restricted_to_rule(b, "G", &b.step(g.0), &b.step(rule.0), line);
        let to_rule = derivative_of_rule(
            b,
            "G",
            &b.step(a.0),
            &b.step(bb.0),
            &b.step(g.0),
            &restricted,
            line,
        );
        // The identity on ℝ has derivative 1, and so on (a, b), which is open.
        let at_real = "( ph /\\ x e. RR )";
        let identity = b.ap(
            "dvmptid",
            &binds! {"ph" => ph.clone(), "S" => b.class("RR"), "x" => x.clone()},
            &[&over_reals(b, "ph")],
        );
        let one_at = |ctx: &str| {
            b.ap(
                "a1i",
                &binds! {"ph" => b.wff("1 e. CC"), "ps" => b.wff(ctx)},
                &[&b.step("ax-1cn")],
            )
        };
        let on_open = b.ap(
            "dvmptres",
            &binds! {"ph" => ph.clone(), "S" => b.class("RR"), "X" => b.class("RR"),
            "Y" => b.class(OPEN), "A" => b.class("x"), "B" => b.class("1"),
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
                &b.ap(
                    "a1i",
                    &binds! {"ph" => b.wff(&format!("{OPEN} C_ RR")), "ps" => ph.clone()},
                    &[&b.ap(
                        "ioossre",
                        &binds! {"A" => b.class("A"), "B" => b.class("B")},
                        &[],
                    )],
                ),
                &real_topology(b),
                &b.ap("eqid", &binds! {"A" => b.class(K)}, &[]),
                &b.ap(
                    "a1i",
                    &binds! {"ph" => b.wff(&format!("{OPEN} e. {T}")), "ps" => ph.clone()},
                    &[&b.ap(
                        "iooretop",
                        &binds! {"A" => b.class("A"), "B" => b.class("B")},
                        &[],
                    )],
                ),
            ],
        );
        let x_complex = b.ap(
            "recnd",
            &binds! {"ph" => b.wff(&at), "A" => b.class("x")},
            &[&b.ap(
                "syl",
                &binds! {"ph" => b.wff(&at), "ps" => b.wff(&format!("x e. {OPEN}")),
                "ch" => b.wff("x e. RR")},
                &[
                    &b.ap(
                        "simpr",
                        &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("x e. {OPEN}"))},
                        &[],
                    ),
                    &b.ap(
                        "elioore",
                        &binds! {"A" => b.class("x"), "B" => b.class("A"), "C" => b.class("B")},
                        &[],
                    ),
                ],
            )],
        );
        let m_complex = b.ap(
            "recnd",
            &binds! {"ph" => ph.clone(), "A" => b.class("M")},
            &[&b.step(m.0)],
        );
        let scaled = b.ap(
            "dvmptcmul",
            &binds! {"ph" => ph.clone(), "S" => b.class("RR"), "X" => b.class(OPEN),
            "A" => b.class("x"), "B" => b.class("1"), "V" => b.class("CC"),
            "C" => b.class("M"), "x" => x.clone()},
            &[
                &over_reals(b, "ph"),
                &x_complex,
                &one_at(&at),
                &on_open,
                &m_complex,
            ],
        );
        let slope = b.ap(
            "mpteq2dva",
            &binds! {"ph" => ph.clone(), "x" => x.clone(), "A" => b.class(OPEN),
            "B" => b.class("( M x. 1 )"), "C" => b.class("M")},
            &[&b.ap(
                "mulridd",
                &binds! {"ph" => b.wff(&at), "A" => b.class("M")},
                &[&b.ap(
                    "adantr",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff("M e. CC"),
                    "ch" => b.wff(&format!("x e. {OPEN}"))},
                    &[&m_complex],
                )],
            )],
        );
        let whole = "( RR _D G )";
        let ruled = format!("( RR _D ( x e. {OPEN} |-> {line} ) )");
        let times_one = format!("( x e. {OPEN} |-> ( M x. 1 ) )");
        let constant = format!("( x e. {OPEN} |-> M )");
        b.ap(
            "eqtrd",
            &binds! {"ph" => ph.clone(), "A" => b.class(whole), "B" => b.class(&times_one),
            "C" => b.class(&constant)},
            &[
                &b.ap(
                    "eqtrd",
                    &binds! {"ph" => ph, "A" => b.class(whole), "B" => b.class(&ruled),
                    "C" => b.class(&times_one)},
                    &[&to_rule, &scaled],
                ),
                &slope,
            ],
        )
    };
    lemma(b, "gdvlinmap", statement, &all, proof)
}

const LINE: [(&str, &str); 5] = [
    ("", "|- ( ph -> A e. RR )"),
    ("", "|- ( ph -> B e. RR )"),
    ("", "|- ( ph -> M e. RR )"),
    ("", "|- ( ph -> G : ( A [,] B ) --> RR )"),
    (
        "",
        "|- ( ph -> A. x e. ( A [,] B ) ( G ` x ) = ( M x. x ) )",
    ),
];

const LINE_BINDS: [(&str, &str); 4] = [("A", "A"), ("B", "B"), ("M", "M"), ("G", "G")];

/// ( ( ph /\ x e. ( A (,) B ) ) -> M e. RR ), from the rule's third
/// hypothesis.
fn slope_real(b: &Builder, label: &str) -> Proof {
    b.ap(
        "adantr",
        &binds! {"ph" => b.wff("ph"), "ps" => b.wff("M e. RR"),
        "ch" => b.wff(&format!("x e. {OPEN}"))},
        &[&b.step(&format!("{label}.3"))],
    )
}

/// `gdvlin` and `gdvlinv`: for `thm:stdlib/calculus/derivative-linear`.
fn line_domain(b: &mut Builder) -> Lemma {
    read_off(
        b,
        "gdvlin",
        &LINE,
        "gdvlinmap",
        &LINE_BINDS,
        "( RR _D G )",
        "M",
        "RR",
        slope_real,
        false,
    )
}

fn line_values(b: &mut Builder) -> Lemma {
    read_off(
        b,
        "gdvlinv",
        &LINE,
        "gdvlinmap",
        &LINE_BINDS,
        "( RR _D G )",
        "M",
        "RR",
        slope_real,
        true,
    )
}

const SUM: [(&str, &str); 8] = [
    ("", "|- ( ph -> A e. RR )"),
    ("", "|- ( ph -> B e. RR )"),
    ("", "|- ( ph -> H : ( A [,] B ) --> RR )"),
    ("", "|- ( ph -> F : ( A [,] B ) --> RR )"),
    ("", "|- ( ph -> G : ( A [,] B ) --> RR )"),
    (
        "",
        "|- ( ph -> A. x e. ( A [,] B ) ( H ` x ) = ( ( F ` x ) + ( G ` x ) ) )",
    ),
    ("", "|- ( ph -> dom ( RR _D F ) = ( A (,) B ) )"),
    ("", "|- ( ph -> dom ( RR _D G ) = ( A (,) B ) )"),
];

const SUM_BINDS: [(&str, &str); 5] =
    [("A", "A"), ("B", "B"), ("H", "H"), ("F", "F"), ("G", "G")];

const SLOPES: &str = "( ( ( RR _D F ) ` x ) + ( ( RR _D G ) ` x ) )";

/// ( ( ph /\ x e. ( A (,) B ) ) -> F′(x) + G′(x) e. _V )
fn slopes_set(b: &Builder, _label: &str) -> Proof {
    b.ap(
        "a1i",
        &binds! {"ph" => b.wff(&format!("{SLOPES} e. _V")),
        "ps" => b.wff(&format!("( ph /\\ x e. {OPEN} )"))},
        &[&b.ap(
            "ovex",
            &binds! {"A" => b.class("( ( RR _D F ) ` x )"),
            "F" => b.class("+"), "B" => b.class("( ( RR _D G ) ` x )")},
            &[],
        )],
    )
}

/// `gdvadd` and `gdvaddv`: for `thm:stdlib/calculus/derivative-sum`.
fn sum_domain(b: &mut Builder) -> Lemma {
    read_off(
        b,
        "gdvadd",
        &SUM,
        "gdvaddmap",
        &SUM_BINDS,
        "( RR _D H )",
        SLOPES,
        "_V",
        slopes_set,
        false,
    )
}

fn sum_values(b: &mut Builder) -> Lemma {
    read_off(
        b,
        "gdvaddv",
        &SUM,
        "gdvaddmap",
        &SUM_BINDS,
        "( RR _D H )",
        SLOPES,
        "_V",
        slopes_set,
        true,
    )
}

/// `gdvaddmap`: the derivative of a sum on [a, b] is the sum of the
/// derivatives on (a, b).
fn derivative_sum(b: &mut Builder) -> Lemma {
    let a = ("gdvaddmap.1", SUM[0].1);
    let bb = ("gdvaddmap.2", SUM[1].1);
    let h = ("gdvaddmap.3", SUM[2].1);
    let f = ("gdvaddmap.4", SUM[3].1);
    let g = ("gdvaddmap.5", SUM[4].1);
    let rule = ("gdvaddmap.6", SUM[5].1);
    let df = ("gdvaddmap.7", SUM[6].1);
    let dg = ("gdvaddmap.8", SUM[7].1);
    let statement = "|- ( ph -> ( RR _D H ) = ( x e. ( A (,) B ) |-> \
                     ( ( ( RR _D F ) ` x ) + ( ( RR _D G ) ` x ) ) ) )";
    let all = [a, bb, h, f, g, rule, df, dg];
    hypotheses(b, &all);
    let proof = {
        let b: &Builder = b;
        let ph = b.wff("ph");
        let x = b.float("x");
        let at = format!("( ph /\\ x e. {OPEN} )");
        let sum = "( ( F ` x ) + ( G ` x ) )";
        let restricted = restricted_to_rule(b, "H", &b.step(h.0), &b.step(rule.0), sum);
        let to_rule = derivative_of_rule(
            b,
            "H",
            &b.step(a.0),
            &b.step(bb.0),
            &b.step(h.0),
            &restricted,
            sum,
        );
        let within = b.ap(
            "sseldd",
            &binds! {"ph" => b.wff(&at), "A" => b.class(OPEN), "B" => b.class(AB),
            "C" => b.class("x")},
            &[
                &open_within(b, &at),
                &b.ap(
                    "simpr",
                    &binds! {"ph" => ph.clone(), "ps" => b.wff(&format!("x e. {OPEN}"))},
                    &[],
                ),
            ],
        );
        // Each part as a map of its values, with its derivative.
        let part = |name: &str, typed: &str, domain: &str| {
            let value = b.ap(
                "recnd",
                &binds! {"ph" => b.wff(&at), "A" => b.class(&format!("( {name} ` x )"))},
                &[&b.ap(
                    "ffvelcdmd",
                    &binds! {"ph" => b.wff(&at), "F" => b.class(name), "A" => b.class(AB),
                    "B" => b.class("RR"), "C" => b.class("x")},
                    &[
                        &b.ap(
                            "adantr",
                            &binds! {"ph" => ph.clone(),
                            "ps" => b.wff(&format!("{name} : {AB} --> RR")),
                            "ch" => b.wff(&format!("x e. {OPEN}"))},
                            &[&b.step(typed)],
                        ),
                        &within,
                    ],
                )],
            );
            let slope = b.ap(
                "a1i",
                &binds! {"ph" => b.wff(&format!("( ( RR _D {name} ) ` x ) e. _V")),
                "ps" => b.wff(&at)},
                &[&b.ap(
                    "fvex",
                    &binds! {"F" => b.class(&format!("( RR _D {name} )")),
                    "A" => b.class("x")},
                    &[],
                )],
            );
            let derivative = b.ap(
                "gdvmpt",
                &binds! {"ph" => ph.clone(), "A" => b.class("A"), "B" => b.class("B"),
                "F" => b.class(name), "x" => x.clone()},
                &[&b.step(a.0), &b.step(bb.0), &b.step(typed), &b.step(domain)],
            );
            (value, slope, derivative)
        };
        let (fv, fs, fd) = part("F", f.0, df.0);
        let (gv, gs, gd) = part("G", g.0, dg.0);
        let added = b.ap(
            "dvmptadd",
            &binds! {"ph" => ph.clone(), "S" => b.class("RR"), "X" => b.class(OPEN),
            "A" => b.class("( F ` x )"), "B" => b.class("( ( RR _D F ) ` x )"),
            "V" => b.class("_V"), "C" => b.class("( G ` x )"),
            "D" => b.class("( ( RR _D G ) ` x )"), "W" => b.class("_V"), "x" => x.clone()},
            &[&over_reals(b, "ph"), &fv, &fs, &fd, &gv, &gs, &gd],
        );
        b.ap(
            "eqtrd",
            &binds! {"ph" => ph, "A" => b.class("( RR _D H )"),
            "B" => b.class(&format!("( RR _D ( x e. {OPEN} |-> {sum} ) )")),
            "C" => b.class(&format!("( x e. {OPEN} |-> {SLOPES} )"))},
            &[&to_rule, &added],
        )
    };
    lemma(b, "gdvaddmap", statement, &all, proof)
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
        let sum = "( ( F ` x ) + ( G ` x ) )";
        let map = format!("( x e. D |-> {sum} )");
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
        let is_map = as_rule(b, "H", &b.step(h.0), &b.step(rule.0), sum);
        continuous_real(b, "H", &b.step(h.0), &is_map, &map, &added)
    };
    lemma(b, "gcncfadd", statement, &all, proof)
}

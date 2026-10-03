//! Parallels, sides of a line and angles along one, for `proved.mm`.
//!
//! The angle sum is proved as a school text proves it: draw the parallel to
//! one side through the opposite vertex, read off two pairs of alternate
//! angles, and see the three angles at the vertex make a straight line. Three
//! items carry that, and set.mm states none of them: `parallel-through`,
//! `alternate-angles` and `angles-on-a-line`. Each says what a figure shows,
//! and over ℂ each is a fact about quotients of differences: two lines are
//! parallel when the quotient of their directions is real, a point's side of
//! a line is the sign of an imaginary part, and an angle is the argument of
//! a quotient.
//!
//! The proofs here are long chains of small identities, and a step is
//! written by naming its lemma and the proofs it rests on: `Prover::by`
//! reads the lemma's variables off what those proofs prove, so that only
//! what nothing fixes is written by hand.

use std::collections::BTreeSet;

use indexmap::IndexMap;

use crate::mm::kernel::{match_term, same};
use crate::mm::library::render;
use crate::mm::{Builder, Proof, Term};
use crate::proofs::Lemma;

pub const HEAD: &str =
    "$( Parallels: lines through a point, the sides of a line, and the
   angles along one, as the angle sum asks of them. $)

$( `angval` and `angneg` read a value of the angle by substituting for the
   two names `df-ang` binds, and ask that they be free of what is
   substituted, as in the geometry block. $)
$d x y $.
$d x P $.  $d y P $.
$d x Q $.  $d y Q $.
$d x R $.  $d y R $.
$d x S $.  $d y S $.
$d x T $.  $d y T $.
$d x X $.  $d y X $.
$d x Y $.  $d y Y $.
$d x M $.  $d y M $.
$( `eflogeq` names the whole number of turns n, which `rexlimdva` then
   discharges, so it is free of the three numbers it counts the turns of. $)
$d n A $.  $d n B $.  $d n C $.

";

/// A proof, and the formula it proves.
#[derive(Clone)]
pub(super) struct Said {
    pub(super) says: Term,
    pub(super) proof: Proof,
}

/// Steps applied by their lemma, with the lemma's variables read off the
/// proofs a step rests on.
pub(super) struct Prover<'a> {
    pub(super) b: &'a Builder,
}

impl Prover<'_> {
    /// A formula or a class in set.mm's notation, as a term.
    pub(super) fn term(&self, text: &str, start: &str) -> Term {
        let tokens: Vec<&str> = text.split_whitespace().collect();
        self.b
            .syntax()
            .parse(&tokens, start)
            .unwrap_or_else(|_| panic!("{text:?} is not a {start}"))
    }

    pub(super) fn show(&self, term: &Term) -> String {
        render(&term.rpn(&self.b.flabel), &self.b.sigs)
    }

    /// `label` applied to `given`, one proof for each of its hypotheses in
    /// order. Its variables are what matching the hypotheses against what
    /// `given` proves makes them, and `fixed` gives those no hypothesis
    /// mentions, in set.mm's notation.
    pub(super) fn by(
        &self,
        label: &str,
        given: &[&Said],
        fixed: &[(&str, &str)],
    ) -> Said {
        let sig = self
            .b
            .sigs
            .get(label)
            .unwrap_or_else(|| panic!("no label {label}"))
            .clone();
        let variables: BTreeSet<String> =
            sig.floats.iter().map(|(_, v)| v.clone()).collect();
        let mut binding: IndexMap<String, Term> = IndexMap::new();
        for (var, text) in fixed {
            let code = sig
                .floats
                .iter()
                .find(|(_, v)| v == var)
                .map(|(c, _)| c.clone())
                .unwrap_or_else(|| panic!("{label} has no variable {var}"));
            binding.insert(var.to_string(), self.term(text, &code));
        }
        assert_eq!(
            sig.essentials.len(),
            given.len(),
            "{label} takes {} hypotheses",
            sig.essentials.len()
        );
        for (n, (hyp, fact)) in sig.essentials.iter().zip(given).enumerate() {
            let tokens: Vec<&str> = hyp[1..].iter().map(String::as_str).collect();
            let pattern = self
                .b
                .syntax()
                .parse(&tokens, "wff")
                .unwrap_or_else(|_| panic!("{label}'s hypothesis does not parse"));
            binding = match_term(&pattern, &fact.says, &binding, &variables)
                .unwrap_or_else(|| {
                    panic!(
                        "{label}'s hypothesis {} is `{}` and is handed `{}`",
                        n + 1,
                        hyp[1..].join(" "),
                        self.show(&fact.says)
                    )
                });
        }
        let statement = self
            .b
            .syntax()
            .statement(&sig)
            .unwrap_or_else(|_| panic!("{label}'s statement does not parse"));
        for (_, var) in &sig.floats {
            if !binding.contains_key(var) {
                panic!("{label} leaves {var} open; fix it");
            }
        }
        let says = statement.substitute(&binding);
        let binds = binding
            .iter()
            .map(|(v, t)| (v.clone(), t.rpn(&self.b.flabel).to_string()))
            .collect();
        let proofs: Vec<&Proof> = given.iter().map(|g| &g.proof).collect();
        Said {
            says,
            proof: self.b.ap(label, &binds, &proofs),
        }
    }

    /// A closed theorem `label`, ( a -> b ), applied under the antecedent the
    /// `given` proofs share: one proof of a, or one of each conjunct of a
    /// two- or three-way conjunction, by `syl`, `syl2anc` or `syl3anc`. The
    /// theorem's variables are read off what the proofs conclude.
    pub(super) fn apply(
        &self,
        label: &str,
        given: &[&Said],
        fixed: &[(&str, &str)],
    ) -> Said {
        let sig = self
            .b
            .sigs
            .get(label)
            .unwrap_or_else(|| panic!("no label {label}"))
            .clone();
        let variables: BTreeSet<String> =
            sig.floats.iter().map(|(_, v)| v.clone()).collect();
        let statement = self
            .b
            .syntax()
            .statement(&sig)
            .unwrap_or_else(|_| panic!("{label}'s statement does not parse"));
        assert_eq!(
            statement.label(),
            Some("wi"),
            "{label} is not an implication"
        );
        let antecedent = &statement.children()[0];
        let pieces: Vec<Term> = match given.len() {
            1 => vec![antecedent.clone()],
            2 | 3 => antecedent.children().to_vec(),
            n => panic!("{label} applied to {n} proofs"),
        };
        assert_eq!(
            pieces.len(),
            given.len(),
            "{label}'s antecedent has another shape"
        );
        let mut binding: IndexMap<String, Term> = IndexMap::new();
        for (var, text) in fixed {
            let code = sig
                .floats
                .iter()
                .find(|(_, v)| v == var)
                .map(|(c, _)| c.clone())
                .unwrap_or_else(|| panic!("{label} has no variable {var}"));
            binding.insert(var.to_string(), self.term(text, &code));
        }
        for (piece, fact) in pieces.iter().zip(given) {
            let consequent = &fact.says.children()[1];
            binding = match_term(piece, consequent, &binding, &variables)
                .unwrap_or_else(|| {
                    panic!(
                        "{label} wants `{}` and is handed `{}`",
                        self.show(piece),
                        self.show(consequent)
                    )
                });
        }
        let fixed: Vec<(String, String)> = binding
            .iter()
            .map(|(v, t)| (v.clone(), self.show(t)))
            .collect();
        let fixed: Vec<(&str, &str)> = fixed
            .iter()
            .map(|(v, t)| (v.as_str(), t.as_str()))
            .collect();
        let closed = self.by(label, &[], &fixed);
        let chain = ["syl", "syl2anc", "syl3anc"][given.len() - 1];
        let mut all: Vec<&Said> = given.to_vec();
        all.push(&closed);
        self.by(chain, &all, &[])
    }

    /// `said`, having checked it proves `text`.
    pub(super) fn is(&self, said: Said, text: &str) -> Said {
        let want = self.term(text, "wff");
        if !same(&said.says, &want) {
            panic!("expected `{text}` and proved `{}`", self.show(&said.says));
        }
        said
    }

    /// Each conjunct of a left-nested antecedent, proved from it:
    /// ( ( ( a /\ b ) /\ c ) -> a ) and so on, in the order written.
    pub(super) fn parts(&self, conjuncts: &[&str]) -> Vec<Said> {
        let mut whole = conjuncts[0].to_string();
        let mut out = vec![self.by("id", &[], &[("ph", conjuncts[0])])];
        for next in &conjuncts[1..] {
            out = out
                .iter()
                .map(|p| self.by("adantr", &[p], &[("ch", next)]))
                .collect();
            out.push(self.by("simpr", &[], &[("ph", &whole), ("ps", next)]));
            whole = format!("( {whole} /\\ {next} )");
        }
        out
    }

    /// The antecedent `parts` takes apart, written out.
    pub(super) fn conjoined(conjuncts: &[&str]) -> String {
        let mut whole = conjuncts[0].to_string();
        for next in &conjuncts[1..] {
            whole = format!("( {whole} /\\ {next} )");
        }
        whole
    }

    /// ( a -> ( b -> ( c -> concl ) ) ) from ( ( ( a /\ b ) /\ c ) -> concl ).
    pub(super) fn curried(&self, said: Said, conjuncts: &[&str]) -> Said {
        let mut out = said;
        for n in (1..conjuncts.len()).rev() {
            out = self.by("ex", &[&out], &[("ph", &Self::conjoined(&conjuncts[..n]))]);
        }
        out
    }

    /// The angle's own value: what `df-ang` says `ang` is.
    pub(super) fn ang_defined(&self) -> Said {
        self.by("df-ang", &[], &[("x", "x"), ("y", "y")])
    }
}

/// The statement a lemma registers and is written with, from its proof.
pub(super) fn statement(p: &Prover, said: &Said) -> String {
    format!("|- {}", p.show(&said.says))
}

/// `gangrp`: lengthening one arm of an angle leaves the angle as it was.
///
/// The angle is the argument of the quotient of the arms, and multiplying an
/// arm by a positive number multiplies the quotient by its inverse, whose
/// logarithm is real (`logmul2`, `relogcl`).
fn arm_scaled(b: &mut Builder) -> Lemma {
    let mems = [
        "( X e. CC /\\ X =/= 0 )",
        "( Y e. CC /\\ Y =/= 0 )",
        "M e. RR+",
    ];
    let label = "gangrp";
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&mems);
        let [x, y, m] = <[Said; 3]>::try_from(p.parts(&mems)).ok().unwrap();
        let xc = p.by("simpld", &[&x], &[]);
        let xn = p.by("simprd", &[&x], &[]);
        let yc = p.by("simpld", &[&y], &[]);
        let yn = p.by("simprd", &[&y], &[]);
        let mc = p.by("rpcnd", &[&m], &[]);
        let mn = p.by("rpne0d", &[&m], &[]);
        let mx = p.by("mulcld", &[&mc, &xc], &[]);
        let mxn = p.by("mulne0d", &[&mc, &xc, &mn, &xn], &[]);
        let def = p.ang_defined();
        let value = |arms: [(&Said, &Said, &str); 2]| -> Said {
            let [(a, an, at), (c, cn, ct)] = arms;
            let both = p.by(
                "jca",
                &[&p.by("jca", &[a, an], &[]), &p.by("jca", &[c, cn], &[])],
                &[],
            );
            p.by(
                "syl",
                &[&both, &p.by("angval", &[&def], &[("A", at), ("B", ct)])],
                &[],
            )
        };
        // ( M x. X ) ang Y is the argument of Y / ( M x. X ), which is
        // ( Y / X ) x. ( 1 / M ).
        let scaled = value([(&mx, &mxn, "( M x. X )"), (&yc, &yn, "Y")]);
        let plain = value([(&xc, &xn, "X"), (&yc, &yn, "Y")]);
        let q = p.by("divcld", &[&yc, &xc, &xn], &[]);
        let qn = p.by("divne0d", &[&yc, &xc, &yn, &xn], &[]);
        let regrouped = p.by(
            "eqtrd",
            &[
                &p.by(
                    "eqcomd",
                    &[&p.by("divdiv1d", &[&yc, &xc, &mc, &xn, &mn], &[])],
                    &[],
                ),
                &p.by("divrecd", &[&q, &mc, &mn], &[]),
            ],
            &[],
        );
        // divdiv1d wrote X x. M; the angle wrote M x. X.
        let turned = p.by("mulcomd", &[&xc, &mc], &[]);
        let regrouped = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq2d",
                    &[&p.by("eqcomd", &[&turned], &[])],
                    &[("C", "Y"), ("F", "/")],
                ),
                &regrouped,
            ],
            &[],
        );
        let inv = p.by("syl", &[&m, &p.by("rpreccl", &[], &[("A", "M")])], &[]);
        let logs = p.by(
            "syl3anc",
            &[
                &q,
                &qn,
                &inv,
                &p.by("logmul2", &[], &[("A", "( Y / X )"), ("B", "( 1 / M )")]),
            ],
            &[],
        );
        let im_logs = p.by("fveq2d", &[&logs], &[("F", "Im")]);
        let lq = p.by("logcld", &[&q, &qn], &[]);
        let lr = p.by("relogcld", &[&inv], &[]);
        let lrc = p.by("recnd", &[&lr], &[]);
        let split = p.by("imaddd", &[&lq, &lrc], &[]);
        let zero = p.by("reim0d", &[&lr], &[]);
        let dropped = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq2d",
                    &[&zero],
                    &[("C", "( Im ` ( log ` ( Y / X ) ) )"), ("F", "+")],
                ),
                &p.by(
                    "addridd",
                    &[&p.by("recnd", &[&p.by("imcld", &[&lq], &[])], &[])],
                    &[],
                ),
            ],
            &[],
        );
        let arg = p.by(
            "eqtrd",
            &[
                &p.by(
                    "fveq2d",
                    &[&p.by("fveq2d", &[&regrouped], &[("F", "log")])],
                    &[("F", "Im")],
                ),
                &p.by(
                    "eqtrd",
                    &[&im_logs, &p.by("eqtrd", &[&split, &dropped], &[])],
                    &[],
                ),
            ],
            &[],
        );
        let said = p.by(
            "eqtr4d",
            &[&p.by("eqtrd", &[&scaled, &arg], &[]), &plain],
            &[],
        );
        let said = p.is(
            said,
            &format!("( {g} -> ( ( M x. X ) ang Y ) = ( X ang Y ) )"),
        );
        let text = statement(&p, &said);
        (said, text)
    };
    b.define(label, &text);
    Lemma::new(label, text, said.proof)
}

/// `galtang`: alternate angles, `alternate-angles`.
///
/// Write k for (S − R)/(Q − P), real because the two lines are parallel, and
/// w for (Q − P)/(P − R). That S and Q are on opposite sides of line RP says
/// (k · Im w) · Im w < 0, so k < 0 and S − R is (−k)(P − Q) with −k positive.
/// The angle at R is then the angle between P − Q and P − R (`gangrp`), which
/// negating both arms (`angneg`) makes the angle between Q − P and R − P, and
/// the angle at P is that one read the other way (`gangsym`).
fn alternate(b: &mut Builder) -> Lemma {
    let conjuncts = [
        "P e. CC",
        "Q e. CC",
        "R e. CC",
        "S e. CC",
        "-. Q = P",
        "-. R = P",
        "( ( S - R ) / ( Q - P ) ) e. RR",
        "( ( Im ` ( ( S - R ) / ( P - R ) ) ) x. ( Im ` ( ( Q - R ) / ( P - R ) ) ) ) < 0",
    ];
    let label = "galtang";
    let (said, text) = {
        let p = Prover { b };
        let h = p.parts(&conjuncts);
        let (pc, qc, rc, sc) = (&h[0], &h[1], &h[2], &h[3]);
        let (qp, rp, k_re, opp) = (&h[4], &h[5], &h[6], &h[7]);
        let qp = p.by("neqned", &[qp], &[]);
        let pr = p.by("necomd", &[&p.by("neqned", &[rp], &[])], &[]);
        let u = p.by("subcld", &[qc, pc], &[]);
        let un = p.by("subne0d", &[qc, pc, &qp], &[]);
        let v = p.by("subcld", &[pc, rc], &[]);
        let vn = p.by("subne0d", &[pc, rc, &pr], &[]);
        let sr = p.by("subcld", &[sc, rc], &[]);
        let kc = p.by("recnd", &[k_re], &[]);
        let w = p.by("divcld", &[&u, &v, &vn], &[]);
        let wi = p.by("imcld", &[&w], &[]);

        // S − R = k (Q − P).
        let back = p.by("divcan1d", &[&sr, &u, &un], &[]);
        // (S − R)/(P − R) = k w.
        let first = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq1d",
                    &[&p.by("eqcomd", &[&back], &[])],
                    &[("C", "( P - R )"), ("F", "/")],
                ),
                &p.by("divassd", &[&kc, &u, &v, &vn], &[]),
            ],
            &[],
        );
        let im_first = p.by(
            "eqtrd",
            &[
                &p.by("fveq2d", &[&first], &[("F", "Im")]),
                &p.by("immul2d", &[k_re, &w], &[]),
            ],
            &[],
        );
        // (Q − R)/(P − R) = w + 1, whose imaginary part is Im w.
        let sum = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq1d",
                    &[&p.by("eqcomd", &[&p.by("npncand", &[qc, pc, rc], &[])], &[])],
                    &[("C", "( P - R )"), ("F", "/")],
                ),
                &p.by("divdird", &[&u, &v, &v, &vn], &[]),
            ],
            &[],
        );
        let sum = p.by(
            "eqtrd",
            &[
                &sum,
                &p.by(
                    "oveq2d",
                    &[&p.by("dividd", &[&v, &vn], &[])],
                    &[("C", "( ( Q - P ) / ( P - R ) )"), ("F", "+")],
                ),
            ],
            &[],
        );
        let one = p.by("ax-1cn", &[], &[]);
        let one = p.by("a1i", &[&one], &[("ps", &Prover::conjoined(&conjuncts))]);
        let im_second = p.by(
            "eqtrd",
            &[
                &p.by("fveq2d", &[&sum], &[("F", "Im")]),
                &p.by("imaddd", &[&w, &one], &[]),
            ],
            &[],
        );
        let im1 = p.by(
            "a1i",
            &[&p.by("im1", &[], &[])],
            &[("ps", &Prover::conjoined(&conjuncts))],
        );
        let im_second = p.by(
            "eqtrd",
            &[
                &im_second,
                &p.by(
                    "eqtrd",
                    &[
                        &p.by(
                            "oveq2d",
                            &[&im1],
                            &[("C", "( Im ` ( ( Q - P ) / ( P - R ) ) )"), ("F", "+")],
                        ),
                        &p.by("addridd", &[&p.by("recnd", &[&wi], &[])], &[]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        // So the product the hypothesis names is ( k x. Im w ) x. Im w.
        let product = p.by("oveq12d", &[&im_first, &im_second], &[("F", "x.")]);
        let below = p.by(
            "mpbid",
            &[opp, &p.by("breq1d", &[&product], &[("C", "0"), ("R", "<")])],
            &[],
        );
        // k < 0: were 0 <_ k, the product would be k times a square.
        let kw = p.by("remulcld", &[k_re, &wi], &[]);
        let prod_re = p.by("remulcld", &[&kw, &wi], &[]);
        let zero_re = p.by(
            "a1i",
            &[&p.by("0re", &[], &[])],
            &[("ps", &Prover::conjoined(&conjuncts))],
        );
        let not_ge = p.by(
            "mpbid",
            &[&below, &p.by("ltnled", &[&prod_re, &zero_re], &[])],
            &[],
        );
        let g = Prover::conjoined(&conjuncts);
        let lift = |s: &Said| {
            p.by("adantr", &[s], &[("ch", "0 <_ ( ( S - R ) / ( Q - P ) )")])
        };
        let k_ge = p.by(
            "simpr",
            &[],
            &[("ph", &g), ("ps", "0 <_ ( ( S - R ) / ( Q - P ) )")],
        );
        let square = p.by("msqge0d", &[&lift(&wi)], &[]);
        let ge = p.by(
            "mulge0d",
            &[
                &lift(k_re),
                &p.by("remulcld", &[&lift(&wi), &lift(&wi)], &[]),
                &k_ge,
                &square,
            ],
            &[],
        );
        let ge = p.by(
            "breqtrrd",
            &[
                &ge,
                &p.by(
                    "mulassd",
                    &[
                        &lift(&kc),
                        &p.by("recnd", &[&lift(&wi)], &[]),
                        &p.by("recnd", &[&lift(&wi)], &[]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let k_ge_not = p.by("pm2.65da", &[&ge, &lift(&not_ge)], &[]);
        let k_neg = p.by(
            "mpbird",
            &[&k_ge_not, &p.by("ltnled", &[k_re, &zero_re], &[])],
            &[],
        );
        // −k is positive, and S − R = (−k)(P − Q).
        let m = p.by(
            "mpbird",
            &[
                &k_neg,
                &p.by(
                    "syl",
                    &[
                        k_re,
                        &p.by("negelrp", &[], &[("A", "( ( S - R ) / ( Q - P ) )")]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let flipped = p.by(
            "eqtrd",
            &[
                &p.by("eqcomd", &[&back], &[]),
                &p.by("eqcomd", &[&p.by("mul2negd", &[&kc, &u], &[])], &[]),
            ],
            &[],
        );
        let flipped = p.by(
            "eqtrd",
            &[
                &flipped,
                &p.by(
                    "oveq2d",
                    &[&p.by("negsubdi2d", &[qc, pc], &[])],
                    &[("C", "-u ( ( S - R ) / ( Q - P ) )"), ("F", "x.")],
                ),
            ],
            &[],
        );
        // The angle at R is the angle between P − Q and P − R.
        let pq = p.by("subcld", &[pc, qc], &[]);
        let pqn = p.by("subne0d", &[pc, qc, &p.by("necomd", &[&qp], &[])], &[]);
        let at_r = p.by("oveq1d", &[&flipped], &[("C", "( P - R )"), ("F", "ang")]);
        let arms = p.by(
            "jca",
            &[
                &p.by("jca", &[&pq, &pqn], &[]),
                &p.by("jca", &[&v, &vn], &[]),
            ],
            &[],
        );
        let scaled = p.by(
            "syl",
            &[
                &p.by("jca", &[&arms, &m], &[]),
                &p.by(
                    "gangrp",
                    &[],
                    &[
                        ("X", "( P - Q )"),
                        ("Y", "( P - R )"),
                        ("M", "-u ( ( S - R ) / ( Q - P ) )"),
                    ],
                ),
            ],
            &[],
        );
        let at_r = p.by("eqtrd", &[&at_r, &scaled], &[]);
        // Negating both arms: P − Q is −(Q − P) and P − R is −(R − P).
        let rpd = p.by("subcld", &[rc, pc], &[]);
        let rpn = p.by("subne0d", &[rc, pc, &p.by("necomd", &[&pr], &[])], &[]);
        let negs = p.by(
            "oveq12d",
            &[
                &p.by("eqcomd", &[&p.by("negsubdi2d", &[qc, pc], &[])], &[]),
                &p.by("eqcomd", &[&p.by("negsubdi2d", &[rc, pc], &[])], &[]),
            ],
            &[("F", "ang")],
        );
        let unneg = p.by(
            "syl",
            &[
                &p.by(
                    "jca",
                    &[
                        &p.by("jca", &[&u, &un], &[]),
                        &p.by("jca", &[&rpd, &rpn], &[]),
                    ],
                    &[],
                ),
                &p.by(
                    "angneg",
                    &[&p.ang_defined()],
                    &[("A", "( Q - P )"), ("B", "( R - P )")],
                ),
            ],
            &[],
        );
        let at_r = p.by(
            "eqtrd",
            &[&at_r, &p.by("eqtrd", &[&negs, &unneg], &[])],
            &[],
        );
        let sizes = p.by("fveq2d", &[&at_r], &[("F", "abs")]);
        let read_back = p.by(
            "syl",
            &[
                &p.by(
                    "jca",
                    &[
                        &p.by("jca", &[&u, &un], &[]),
                        &p.by("jca", &[&rpd, &rpn], &[]),
                    ],
                    &[],
                ),
                &p.by("gangsym", &[], &[("A", "( Q - P )"), ("B", "( R - P )")]),
            ],
            &[],
        );
        let said = p.by("eqtrd", &[&sizes, &read_back], &[]);
        let said = p.is(
            said,
            &format!("( {g} -> ( abs ` ( ( S - R ) ang ( P - R ) ) ) = ( abs ` ( ( R - P ) ang ( Q - P ) ) ) )"),
        );
        let said = p.curried(said, &conjuncts);
        let text = statement(&p, &said);
        (said, text)
    };
    b.define(label, &text);
    Lemma::new(label, text, said.proof)
}

impl Prover<'_> {
    /// `said` under one more conjunct of its antecedent.
    pub(super) fn lift(&self, said: &Said, extra: &str) -> Said {
        self.by("adantr", &[said], &[("ch", extra)])
    }

    /// A closed fact under the antecedent `g`.
    pub(super) fn always(&self, said: &Said, g: &str) -> Said {
        self.by("a1i", &[said], &[("ps", g)])
    }

    /// ( g -> ( ( ( a /\ b ) /\ c ) ... ) ), from a proof of each under g.
    pub(super) fn joined(&self, parts: &[&Said]) -> Said {
        let mut out = parts[0].clone();
        for next in &parts[1..] {
            out = self.by("jca", &[&out, next], &[]);
        }
        out
    }

    /// ( g -> x =/= 0 ), from ( g -> ( Im ` x ) =/= 0 ): a number whose
    /// imaginary part is not 0 is not 0, since 0's is (`im0`).
    pub(super) fn nonzero(&self, x: &str, g: &str, im_apart: &Said) -> Said {
        let read = self.by("fveq2", &[], &[("A", x), ("B", "0"), ("F", "Im")]);
        let zero = self.by("eqtrdi", &[&read, &self.by("im0", &[], &[])], &[]);
        let back = self.by("necon3d", &[&self.always(&zero, g)], &[]);
        self.by("mpd", &[im_apart, &back], &[])
    }

    /// ( g -> ( Im ` ( _i x. y ) ) = y ), for y real: the imaginary part of
    /// 0 + i·y (`crim`).
    pub(super) fn im_times_i(&self, y: &str, g: &str, real: &Said) -> Said {
        let zero = self.always(&self.by("0re", &[], &[]), g);
        let read = self.by(
            "syl2anc",
            &[&zero, real, &self.by("crim", &[], &[("A", "0"), ("B", y)])],
            &[],
        );
        let product = self.by(
            "mulcld",
            &[
                &self.always(&self.by("ax-icn", &[], &[]), g),
                &self.by("recnd", &[real], &[]),
            ],
            &[],
        );
        self.by(
            "eqtr3d",
            &[
                &self.by(
                    "fveq2d",
                    &[&self.by("addlidd", &[&product], &[])],
                    &[("F", "Im")],
                ),
                &read,
            ],
            &[],
        )
    }
}

/// Whether `t` holds `v` anywhere.
fn mentions(t: &Term, v: &Term) -> bool {
    same(t, v) || t.children().iter().any(|k| mentions(k, v))
}

impl Prover<'_> {
    /// From `eq`, ( ph -> v = w ), that a term holding v equals the same
    /// term holding w, or a formula holding v says what the same formula
    /// holding w says: one congruence lemma for each node on the way down to
    /// every v. None where `t` does not hold v.
    pub(super) fn cong(&self, eq: &Said, v: &Term, t: &Term) -> Option<Said> {
        if same(t, v) {
            return Some(eq.clone());
        }
        if !mentions(t, v) {
            return None;
        }
        let kids = t.children();
        let moved: Vec<Option<Said>> =
            kids.iter().map(|k| self.cong(eq, v, k)).collect();
        let text = |i: usize| self.show(&kids[i]);
        let label = t.label().unwrap_or("");
        // Two-place nodes: the lemma for both places, the first, the second,
        // the name the unchanged place takes in each, and any fixed operator.
        let two = |both: &str,
                   first: &str,
                   second: &str,
                   other: &str,
                   op: Option<(&str, usize)>|
         -> Said {
            let mut fixed: Vec<(String, String)> = Vec::new();
            if let Some((name, at)) = op {
                fixed.push((name.to_string(), text(at)));
            }
            let (lemma, given): (&str, Vec<&Said>) = match (&moved[0], &moved[1]) {
                (Some(a), Some(b)) => (both, vec![a, b]),
                (Some(a), None) => {
                    fixed.push((other.to_string(), text(1)));
                    (first, vec![a])
                }
                (None, Some(b)) => {
                    fixed.push((other.to_string(), text(0)));
                    (second, vec![b])
                }
                (None, None) => panic!("{label} holds v in a place it cannot rewrite"),
            };
            let fixed: Vec<(&str, &str)> = fixed
                .iter()
                .map(|(a, b)| (a.as_str(), b.as_str()))
                .collect();
            self.by(lemma, &given, &fixed)
        };
        Some(match label {
            "co" => two("oveq12d", "oveq1d", "oveq2d", "C", Some(("F", 2))),
            "wbr" => two("breq12d", "breq1d", "breq2d", "C", Some(("R", 2))),
            "wcel" => two("eleq12d", "eleq1d", "eleq2d", "C", None),
            "wne" => two("neeq12d", "neeq1d", "neeq2d", "C", None),
            "wceq" => two("eqeq12d", "eqeq1d", "eqeq2d", "C", None),
            "wa" => two("anbi12d", "anbi1d", "anbi2d", "th", None),
            "cfv" => self.by(
                "fveq2d",
                &[moved[0].as_ref().expect("a function's argument")],
                &[("F", &text(1))],
            ),
            "cneg" => self.by("negeqd", &[moved[0].as_ref().unwrap()], &[]),
            "wn" => self.by("notbid", &[moved[0].as_ref().unwrap()], &[]),
            "w3a" => {
                let ph = self.show(&eq.says.children()[0]);
                let each: Vec<Said> = (0..3)
                    .map(|i| {
                        moved[i].clone().unwrap_or_else(|| {
                            self.by("biidd", &[], &[("ph", &ph), ("ps", &text(i))])
                        })
                    })
                    .collect();
                self.by("3anbi123d", &[&each[0], &each[1], &each[2]], &[])
            }
            other => panic!("no congruence for {other}"),
        })
    }

    /// ( g -> ( ( y - x ) / ( x - y ) ) = -u 1 ), from x and y being numbers
    /// and x − y not 0.
    pub(super) fn minus_one(&self, x: &Said, y: &Said, apart: &Said) -> Said {
        let d = self.by("subcld", &[x, y], &[]);
        let turned = self.by("eqcomd", &[&self.by("negsubdi2d", &[x, y], &[])], &[]);
        let below = self.show(&d.says.children()[1].children()[0]);
        let out = self.by("oveq1d", &[&turned], &[("C", &below), ("F", "/")]);
        let out = self.by(
            "eqtrd",
            &[
                &out,
                &self.by("eqcomd", &[&self.by("divnegd", &[&d, &d, apart], &[])], &[]),
            ],
            &[],
        );
        self.by(
            "eqtrd",
            &[
                &out,
                &self.by("negeqd", &[&self.by("dividd", &[&d, apart], &[])], &[]),
            ],
            &[],
        )
    }

    /// ( g -> ( Im ` w ) =/= 0 ), from w = a / b, b not 0, and a / b not
    /// real: a number off the real line has an imaginary part.
    pub(super) fn off_line(&self, w: &Said, eq: &Said, not_real: &Said) -> Said {
        let not_w = self.by(
            "mtbird",
            &[not_real, &self.by("eleq1d", &[eq], &[("C", "RR")])],
            &[],
        );
        let im_zero = self.apply("reim0b", &[w], &[]);
        self.by(
            "neqned",
            &[&self.by("mtbid", &[&not_w, &im_zero], &[])],
            &[],
        )
    }
}

/// `gargpos`: three numbers above the real line whose product is a negative
/// real have arguments adding to π.
///
/// The three logarithms add to a logarithm of the product, up to a whole
/// number of turns (`eflogeq`): their imaginary parts add to π + 2πn. Each
/// argument is between 0 and π (`argimgt0`), so the sum is between 0 and 3π,
/// which leaves n = 0.
fn arguments_positive(b: &mut Builder) -> Lemma {
    let t = "( ( A x. B ) x. C )";
    let conjuncts = [
        "A e. CC",
        "B e. CC",
        "C e. CC",
        "0 < ( Im ` A )",
        "0 < ( Im ` B )",
        "0 < ( Im ` C )",
        "( ( A x. B ) x. C ) e. RR",
        "( ( A x. B ) x. C ) < 0",
    ];
    let label = "gargpos";
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&conjuncts);
        let h = p.parts(&conjuncts);
        let (t_re, t_neg) = (&h[6], &h[7]);
        let names = ["A", "B", "C"];
        // Each number is not 0, has a logarithm, and an argument in (0, π).
        let mut nz = Vec::new();
        let mut logs = Vec::new();
        let mut args = Vec::new();
        for (i, x) in names.iter().enumerate() {
            let (cc, up) = (&h[i], &h[i + 3]);
            let n = p.nonzero(x, &g, &p.by("gt0ne0d", &[up], &[]));
            logs.push(p.by("logcld", &[cc, &n], &[]));
            nz.push(n);
            let within = p.by(
                "syl2anc",
                &[cc, up, &p.by("argimgt0", &[], &[("A", x)])],
                &[],
            );
            args.push(within);
        }
        let theta = |x: &str| format!("( Im ` ( log ` {x} ) )");
        let l = "( ( ( log ` A ) + ( log ` B ) ) + ( log ` C ) )".to_string();
        let l_ab = p.by("addcld", &[&logs[0], &logs[1]], &[]);
        let l_cc = p.by("addcld", &[&l_ab, &logs[2]], &[]);
        // exp L = A B C.
        let efadd = |a: &Said, c: &Said, at: &str, ct: &str| -> Said {
            p.by(
                "syl2anc",
                &[a, c, &p.by("efadd", &[], &[("A", at), ("B", ct)])],
                &[],
            )
        };
        let eflog = |i: usize| -> Said {
            p.by(
                "syl2anc",
                &[&h[i], &nz[i], &p.by("eflog", &[], &[("A", names[i])])],
                &[],
            )
        };
        let e_ab = p.by(
            "eqtrd",
            &[
                &efadd(&logs[0], &logs[1], "( log ` A )", "( log ` B )"),
                &p.by("oveq12d", &[&eflog(0), &eflog(1)], &[("F", "x.")]),
            ],
            &[],
        );
        let e_l = p.by(
            "eqtrd",
            &[
                &efadd(
                    &l_ab,
                    &logs[2],
                    "( ( log ` A ) + ( log ` B ) )",
                    "( log ` C )",
                ),
                &p.by("oveq12d", &[&e_ab, &eflog(2)], &[("F", "x.")]),
            ],
            &[],
        );
        let t_c = p.by("recnd", &[t_re], &[]);
        let t_nz = p.by("lt0ne0d", &[t_neg], &[]);
        let turns = p.by(
            "syl3anc",
            &[
                &l_cc,
                &t_c,
                &t_nz,
                &p.by("eflogeq", &[], &[("A", &l), ("B", t), ("n", "n")]),
            ],
            &[],
        );
        let turns = p.by("mpbid", &[&e_l, &turns], &[]);

        // Under a whole number n with L = log t + (i 2π) n.
        let in_z = "n e. ZZ";
        let eq = format!("{l} = ( ( log ` {t} ) + ( ( _i x. ( 2 x. _pi ) ) x. n ) )");
        let gz = format!("( {g} /\\ {in_z} )");
        let gh = format!("( {gz} /\\ {eq} )");
        let up = |s: &Said| p.lift(&p.lift(s, in_z), &eq);
        let n_z = p.lift(&p.by("simpr", &[], &[("ph", &g), ("ps", in_z)]), &eq);
        let said_eq = p.by("simpr", &[], &[("ph", &gz), ("ps", &eq)]);
        let n_re = p.by("zred", &[&n_z], &[]);
        let n_c = p.by("zcnd", &[&n_z], &[]);
        let pi_re = p.always(&p.by("pire", &[], &[]), &gh);
        let pi_c = p.always(&p.by("picn", &[], &[]), &gh);
        let two_re = p.always(&p.by("2re", &[], &[]), &gh);
        let two_pi_re = p.by("remulcld", &[&two_re, &pi_re], &[]);
        let two_pi_c = p.by("recnd", &[&two_pi_re], &[]);
        let i_c = p.always(&p.by("ax-icn", &[], &[]), &gh);
        // Im log t = π, since t is negative.
        let neg_t = p.by("negelrpd", &[&up(t_re), &up(t_neg)], &[]);
        let back_t = p.by("negnegd", &[&up(&t_c)], &[]);
        let log_t = p.by(
            "eqtr3d",
            &[
                &p.by("fveq2d", &[&back_t], &[("F", "log")]),
                &p.by(
                    "syl",
                    &[&neg_t, &p.by("logneg", &[], &[("A", &format!("-u {t}"))])],
                    &[],
                ),
            ],
            &[],
        );
        let lnt_re = p.by("relogcld", &[&neg_t], &[]);
        let ipi = p.by("mulcld", &[&i_c, &pi_c], &[]);
        let im_log_t = p.by(
            "eqtrd",
            &[
                &p.by("fveq2d", &[&log_t], &[("F", "Im")]),
                &p.by("imaddd", &[&p.by("recnd", &[&lnt_re], &[]), &ipi], &[]),
            ],
            &[],
        );
        let im_log_t = p.by(
            "eqtrd",
            &[
                &im_log_t,
                &p.by(
                    "oveq12d",
                    &[
                        &p.by("reim0d", &[&lnt_re], &[]),
                        &p.im_times_i("_pi", &gh, &pi_re),
                    ],
                    &[("F", "+")],
                ),
            ],
            &[],
        );
        let im_log_t =
            p.by("eqtrd", &[&im_log_t, &p.by("addlidd", &[&pi_c], &[])], &[]);
        // Im ( ( i 2π ) n ) = 2π n.
        let tpn = p.by("remulcld", &[&two_pi_re, &n_re], &[]);
        let regroup = p.by("mulassd", &[&i_c, &two_pi_c, &n_c], &[]);
        let im_turns = p.by(
            "eqtrd",
            &[
                &p.by("fveq2d", &[&regroup], &[("F", "Im")]),
                &p.im_times_i("( ( 2 x. _pi ) x. n )", &gh, &tpn),
            ],
            &[],
        );
        // So the arguments add to π + 2π n.
        let lt_c = p.by("logcld", &[&up(&t_c), &up(&t_nz)], &[]);
        let turn_c = p.by(
            "mulcld",
            &[&p.by("mulcld", &[&i_c, &two_pi_c], &[]), &n_c],
            &[],
        );
        let im_l = p.by(
            "eqtrd",
            &[
                &p.by("fveq2d", &[&said_eq], &[("F", "Im")]),
                &p.by("imaddd", &[&lt_c, &turn_c], &[]),
            ],
            &[],
        );
        let im_l = p.by(
            "eqtrd",
            &[
                &im_l,
                &p.by("oveq12d", &[&im_log_t, &im_turns], &[("F", "+")]),
            ],
            &[],
        );
        let split = p.by(
            "eqtrd",
            &[
                &p.by("imaddd", &[&up(&l_ab), &up(&logs[2])], &[]),
                &p.by(
                    "oveq1d",
                    &[&p.by("imaddd", &[&up(&logs[0]), &up(&logs[1])], &[])],
                    &[("C", &theta("C")), ("F", "+")],
                ),
            ],
            &[],
        );
        let sum = format!("( ( {} + {} ) + {} )", theta("A"), theta("B"), theta("C"));
        let s_eq = p.by("eqtr3d", &[&split, &im_l], &[]);
        let s_eq = p.is(
            s_eq,
            &format!("( {gh} -> {sum} = ( _pi + ( ( 2 x. _pi ) x. n ) ) )"),
        );
        // Each argument in (0, π): real, above 0, below π.
        let mut th_re = Vec::new();
        let mut th_pos = Vec::new();
        let mut th_lt = Vec::new();
        for arg in &args {
            let arg = up(arg);
            th_re.push(p.apply("elioore", &[&arg], &[]));
            let ord = p.apply("eliooord", &[&arg], &[]);
            th_pos.push(p.by("simpld", &[&ord], &[]));
            th_lt.push(p.by("simprd", &[&ord], &[]));
        }
        let ab_re = p.by("readdcld", &[&th_re[0], &th_re[1]], &[]);
        let pp_re = p.by("readdcld", &[&pi_re, &pi_re], &[]);
        let s_below = p.by(
            "lt2addd",
            &[
                &ab_re,
                &th_re[2],
                &pp_re,
                &pi_re,
                &p.by(
                    "lt2addd",
                    &[&th_re[0], &th_re[1], &pi_re, &pi_re, &th_lt[0], &th_lt[1]],
                    &[],
                ),
                &th_lt[2],
            ],
            &[],
        );
        let zero_re = p.always(&p.by("0re", &[], &[]), &gh);
        let s_above = p.by(
            "addgt0d",
            &[
                &ab_re,
                &th_re[2],
                &p.by(
                    "addgt0d",
                    &[&th_re[0], &th_re[1], &th_pos[0], &th_pos[1]],
                    &[],
                ),
                &th_pos[2],
            ],
            &[],
        );
        // n < 1: π + 2π n < (π + π) + π, which is π + 2π · 1.
        let one_re = p.always(&p.by("1re", &[], &[]), &gh);
        let pi_rp = p.always(&p.by("pirp", &[], &[]), &gh);
        let two_pi_rp = p.by(
            "rpmulcld",
            &[&p.always(&p.by("2rp", &[], &[]), &gh), &pi_rp],
            &[],
        );
        let twice = p.by("2timesd", &[&pi_c], &[]);
        let three = p.by(
            "eqtrd",
            &[
                &p.by("addassd", &[&pi_c, &pi_c, &pi_c], &[]),
                &p.by(
                    "oveq2d",
                    &[&p.by(
                        "eqtrd",
                        &[
                            &p.by("eqcomd", &[&twice], &[]),
                            &p.by(
                                "eqcomd",
                                &[&p.by("mulridd", &[&two_pi_c], &[])],
                                &[],
                            ),
                        ],
                        &[],
                    )],
                    &[("C", "_pi"), ("F", "+")],
                ),
            ],
            &[],
        );
        let below_one = p.by(
            "breqtrd",
            &[&p.by("eqbrtrrd", &[&s_eq, &s_below], &[]), &three],
            &[],
        );
        let below_one = p.by(
            "mpbird",
            &[
                &below_one,
                &p.by(
                    "ltadd2d",
                    &[&tpn, &p.by("remulcld", &[&two_pi_re, &one_re], &[]), &pi_re],
                    &[],
                ),
            ],
            &[],
        );
        let n_lt_1 = p.by(
            "mpbird",
            &[
                &below_one,
                &p.by("ltmul2d", &[&n_re, &one_re, &two_pi_rp], &[]),
            ],
            &[],
        );
        // −1 < n: π + 2π · (−1) = π − (π + π), below 0 and so below π + 2π n.
        let m1_re = p.by("renegcld", &[&one_re], &[]);
        let m1_c = p.by("recnd", &[&m1_re], &[]);
        let minus = p.by(
            "eqtrd",
            &[
                &p.by("mulcomd", &[&two_pi_c, &m1_c], &[]),
                &p.by("mulm1d", &[&two_pi_c], &[]),
            ],
            &[],
        );
        let minus = p.by(
            "eqtrd",
            &[
                &p.by("oveq2d", &[&minus], &[("C", "_pi"), ("F", "+")]),
                &p.by("negsubd", &[&pi_c, &two_pi_c], &[]),
            ],
            &[],
        );
        let minus = p.by(
            "eqtrd",
            &[
                &minus,
                &p.by("oveq2d", &[&twice], &[("C", "_pi"), ("F", "-")]),
            ],
            &[],
        );
        let more = p.by("ltaddrpd", &[&pi_re, &pi_rp], &[]);
        let under_zero = p.by(
            "mpbird",
            &[&more, &p.by("sublt0d", &[&pi_re, &pp_re], &[])],
            &[],
        );
        let low = p.by("eqbrtrd", &[&minus, &under_zero], &[]);
        let low = p.by(
            "lttrd",
            &[
                &p.by(
                    "readdcld",
                    &[&pi_re, &p.by("remulcld", &[&two_pi_re, &m1_re], &[])],
                    &[],
                ),
                &zero_re,
                &p.by("readdcld", &[&pi_re, &tpn], &[]),
                &low,
                &p.by("breqtrd", &[&s_above, &s_eq], &[]),
            ],
            &[],
        );
        let low = p.by(
            "mpbird",
            &[
                &low,
                &p.by(
                    "ltadd2d",
                    &[&p.by("remulcld", &[&two_pi_re, &m1_re], &[]), &tpn, &pi_re],
                    &[],
                ),
            ],
            &[],
        );
        let m1_lt_n = p.by(
            "mpbird",
            &[&low, &p.by("ltmul2d", &[&m1_re, &n_re, &two_pi_rp], &[])],
            &[],
        );
        // So 0 <_ n, n is in NN0, and n = 0.
        let m1_z = p.always(&p.by("neg1z", &[], &[]), &gh);
        let step_up = p.by(
            "syl2anc",
            &[
                &m1_z,
                &n_z,
                &p.by("zltp1le", &[], &[("M", "-u 1"), ("N", "n")]),
            ],
            &[],
        );
        let ge = p.by("mpbid", &[&m1_lt_n, &step_up], &[]);
        let zero_sum = p.by(
            "eqtrd",
            &[
                &p.by("addcomd", &[&m1_c, &p.by("recnd", &[&one_re], &[])], &[]),
                &p.always(&p.by("1pneg1e0", &[], &[]), &gh),
            ],
            &[],
        );
        let ge = p.by("eqbrtrrd", &[&zero_sum, &ge], &[]);
        let nat = p.by(
            "mpbird",
            &[
                &p.by("jca", &[&n_z, &ge], &[]),
                &p.always(&p.by("elnn0z", &[], &[("N", "n")]), &gh),
            ],
            &[],
        );
        let n_zero = p.by(
            "mpbid",
            &[
                &n_lt_1,
                &p.by("syl", &[&nat, &p.by("nn0lt10b", &[], &[("N", "n")])], &[]),
            ],
            &[],
        );
        let s_pi = p.by(
            "eqtrd",
            &[
                &s_eq,
                &p.by(
                    "oveq2d",
                    &[&p.by(
                        "eqtrd",
                        &[
                            &p.by(
                                "oveq2d",
                                &[&n_zero],
                                &[("C", "( 2 x. _pi )"), ("F", "x.")],
                            ),
                            &p.by("mul01d", &[&two_pi_c], &[]),
                        ],
                        &[],
                    )],
                    &[("C", "_pi"), ("F", "+")],
                ),
            ],
            &[],
        );
        let s_pi = p.by("eqtrd", &[&s_pi, &p.by("addridd", &[&pi_c], &[])], &[]);
        // Each argument is its own size, being positive.
        let size = |i: usize| -> Said {
            p.by(
                "absidd",
                &[
                    &th_re[i],
                    &p.by("ltled", &[&zero_re, &th_re[i], &th_pos[i]], &[]),
                ],
                &[],
            )
        };
        let sizes = p.by(
            "oveq12d",
            &[
                &p.by("oveq12d", &[&size(0), &size(1)], &[("F", "+")]),
                &size(2),
            ],
            &[("F", "+")],
        );
        let done = p.by("eqtrd", &[&sizes, &s_pi], &[]);
        let done = p.by("ex", &[&done], &[]);
        let done = p.by("rexlimdva", &[&done], &[]);
        let said = p.by("mpd", &[&turns, &done], &[]);
        let text = statement(&p, &said);
        (said, text)
    };
    b.define(label, &text);
    Lemma::new(label, text, said.proof)
}

/// `gargsum`: three numbers on one side of the real line whose product is a
/// negative real have argument sizes adding to π.
///
/// The imaginary parts share a sign, which is what the two products say.
/// Above the line it is `gargpos`; below it the conjugates are above, their
/// product is the same real number, and each conjugate's argument is the
/// original's negated (`logcj`), so of the same size.
fn arguments_sum(b: &mut Builder) -> Lemma {
    let conjuncts = [
        "A e. CC",
        "B e. CC",
        "C e. CC",
        "0 < ( ( Im ` A ) x. ( Im ` B ) )",
        "0 < ( ( Im ` A ) x. ( Im ` C ) )",
        "( ( A x. B ) x. C ) e. RR",
        "( ( A x. B ) x. C ) < 0",
    ];
    let label = "gargsum";
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&conjuncts);
        let h = p.parts(&conjuncts);
        let names = ["A", "B", "C"];
        let im: Vec<Said> = (0..3).map(|i| p.by("imcld", &[&h[i]], &[])).collect();
        let ab_apart = p.by(
            "mpbird",
            &[
                &p.by("gt0ne0d", &[&h[3]], &[]),
                &p.by(
                    "mulne0bd",
                    &[
                        &p.by("recnd", &[&im[0]], &[]),
                        &p.by("recnd", &[&im[1]], &[]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let ac_apart = p.by(
            "mpbird",
            &[
                &p.by("gt0ne0d", &[&h[4]], &[]),
                &p.by(
                    "mulne0bd",
                    &[
                        &p.by("recnd", &[&im[0]], &[]),
                        &p.by("recnd", &[&im[2]], &[]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let apart = [
            p.by("simpld", &[&ab_apart], &[]),
            p.by("simprd", &[&ab_apart], &[]),
            p.by("simprd", &[&ac_apart], &[]),
        ];
        let zero_re = p.always(&p.by("0re", &[], &[]), &g);
        let sides = p.by(
            "mpbid",
            &[&apart[0], &p.by("lttri2d", &[&im[0], &zero_re], &[])],
            &[],
        );
        let sum = "( ( ( abs ` ( Im ` ( log ` A ) ) ) + ( abs ` ( Im ` ( log ` B ) ) ) ) + ( abs ` ( Im ` ( log ` C ) ) ) ) = _pi";

        // Above the line: the other two are above it as well.
        let above = {
            let up = "0 < ( Im ` A )";
            let gu = format!("( {g} /\\ {up} )");
            let l = |s: &Said| p.lift(s, up);
            let a_up = p.by("simpr", &[], &[("ph", &g), ("ps", up)]);
            let ge = p.by("ltled", &[&l(&zero_re), &l(&im[0]), &a_up], &[]);
            let other = |i: usize, prod: &Said| -> Said {
                p.apply(
                    "prodgt0",
                    &[&p.joined(&[
                        &p.joined(&[&l(&im[0]), &l(&im[i])]),
                        &p.joined(&[&ge, &l(prod)]),
                    ])],
                    &[],
                )
            };
            let b_up = other(1, &h[3]);
            let c_up = other(2, &h[4]);
            let all = p.joined(&[
                &l(&h[0]),
                &l(&h[1]),
                &l(&h[2]),
                &a_up,
                &b_up,
                &c_up,
                &l(&h[5]),
                &l(&h[6]),
            ]);
            let said = p.apply("gargpos", &[&all], &[]);
            p.is(said, &format!("( {gu} -> {sum} )"))
        };

        // Below the line: the conjugates are above it.
        let below = {
            let down = "( Im ` A ) < 0";
            let gd = format!("( {g} /\\ {down} )");
            let l = |s: &Said| p.lift(s, down);
            let a_down = p.by("simpr", &[], &[("ph", &g), ("ps", down)]);
            let a_neg = p.by(
                "mpbid",
                &[&a_down, &p.by("lt0neg1d", &[&l(&im[0])], &[])],
                &[],
            );
            let a_ge = p.by(
                "ltled",
                &[&l(&zero_re), &p.by("renegcld", &[&l(&im[0])], &[]), &a_neg],
                &[],
            );
            // −Im A and −Im X multiply to Im A · Im X, so −Im X > 0.
            let neg_up = |i: usize, prod: &Said| -> Said {
                let same = p.by(
                    "mul2negd",
                    &[
                        &p.by("recnd", &[&l(&im[0])], &[]),
                        &p.by("recnd", &[&l(&im[i])], &[]),
                    ],
                    &[],
                );
                let prod = p.by("breqtrrd", &[&l(prod), &same], &[]);
                p.apply(
                    "prodgt0",
                    &[&p.joined(&[
                        &p.joined(&[
                            &p.by("renegcld", &[&l(&im[0])], &[]),
                            &p.by("renegcld", &[&l(&im[i])], &[]),
                        ]),
                        &p.joined(&[&a_ge, &prod]),
                    ])],
                    &[],
                )
            };
            let negs = [a_neg.clone(), neg_up(1, &h[3]), neg_up(2, &h[4])];
            // Each conjugate's imaginary part is −Im X, above 0.
            let cj: Vec<Said> =
                (0..3).map(|i| p.by("cjcld", &[&l(&h[i])], &[])).collect();
            let cj_up: Vec<Said> = (0..3)
                .map(|i| {
                    p.by(
                        "breqtrrd",
                        &[&negs[i], &p.by("imcjd", &[&l(&h[i])], &[])],
                        &[],
                    )
                })
                .collect();
            // The conjugates' product is the conjugate of t, which is t.
            let ab = p.by("mulcld", &[&l(&h[0]), &l(&h[1])], &[]);
            let cj_t = p.by(
                "eqtrd",
                &[
                    &p.by("cjmuld", &[&ab, &l(&h[2])], &[]),
                    &p.by(
                        "oveq1d",
                        &[&p.by("cjmuld", &[&l(&h[0]), &l(&h[1])], &[])],
                        &[("C", "( * ` C )"), ("F", "x.")],
                    ),
                ],
                &[],
            );
            let same_t =
                p.by("eqtr3d", &[&cj_t, &p.by("cjred", &[&l(&h[5])], &[])], &[]);
            let t_re = p.by("eqeltrd", &[&same_t, &l(&h[5])], &[]);
            let t_neg = p.by("eqbrtrd", &[&same_t, &l(&h[6])], &[]);
            let all = p.joined(&[
                &cj[0], &cj[1], &cj[2], &cj_up[0], &cj_up[1], &cj_up[2], &t_re, &t_neg,
            ]);
            let conj_sum = p.apply("gargpos", &[&all], &[]);
            // |Im log X*| = |−Im log X| = |Im log X|.
            let size = |i: usize| -> Said {
                let x = names[i];
                let lg =
                    p.apply("logcj", &[&p.joined(&[&l(&h[i]), &l(&apart[i])])], &[]);
                let lx = p.by(
                    "logcld",
                    &[&l(&h[i]), &p.nonzero(x, &gd, &l(&apart[i]))],
                    &[],
                );
                let im_eq = p.by(
                    "eqtrd",
                    &[
                        &p.by("fveq2d", &[&lg], &[("F", "Im")]),
                        &p.by("imcjd", &[&lx], &[]),
                    ],
                    &[],
                );
                p.by(
                    "eqtrd",
                    &[
                        &p.by("fveq2d", &[&im_eq], &[("F", "abs")]),
                        &p.by(
                            "absnegd",
                            &[&p.by("recnd", &[&p.by("imcld", &[&lx], &[])], &[])],
                            &[],
                        ),
                    ],
                    &[],
                )
            };
            let sizes = p.by(
                "oveq12d",
                &[
                    &p.by("oveq12d", &[&size(0), &size(1)], &[("F", "+")]),
                    &size(2),
                ],
                &[("F", "+")],
            );
            let said = p.by("eqtr3d", &[&sizes, &conj_sum], &[]);
            p.is(said, &format!("( {gd} -> {sum} )"))
        };
        let said = p.by("mpjaodan", &[&below, &above, &sides], &[]);
        let text = statement(&p, &said);
        (said, text)
    };
    b.define(label, &text);
    Lemma::new(label, text, said.proof)
}

/// `grecsgn`: 1/Z is on the other side of the real line from Z.
///
/// Im(1/Z) is −Im Z/|Z|² (`recval`), so Im(1/Z) · Im W is negative exactly
/// when Im Z · Im W is positive. A side of a line is the sign of an imaginary
/// part, and the two side hypotheses of `angles-on-a-line` divide by each
/// other's points, so this is how one is read in terms of the other.
fn reciprocal_side(b: &mut Builder) -> Lemma {
    let conjuncts = ["( Z e. CC /\\ Z =/= 0 )", "W e. CC"];
    let label = "grecsgn";
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&conjuncts);
        let h = p.parts(&conjuncts);
        let z = p.by("simpld", &[&h[0]], &[]);
        let zn = p.by("simprd", &[&h[0]], &[]);
        let w = &h[1];
        let size = p.by(
            "rpexpcld",
            &[
                &p.by("absrpcld", &[&z, &zn], &[]),
                &p.always(&p.by("2z", &[], &[]), &g),
            ],
            &[],
        );
        let size_re = p.by("rpred", &[&size], &[]);
        let size_nz = p.by("rpne0d", &[&size], &[]);
        let im_z = p.by("imcld", &[&z], &[]);
        let im_w = p.by("imcld", &[w], &[]);
        // Im ( 1 / Z ) = -u Im Z / |Z|^2.
        let rec = p.apply("recval", &[&h[0]], &[]);
        let im_rec = p.by(
            "eqtrd",
            &[
                &p.by("fveq2d", &[&rec], &[("F", "Im")]),
                &p.by(
                    "imdivd",
                    &[&size_re, &p.by("cjcld", &[&z], &[]), &size_nz],
                    &[],
                ),
            ],
            &[],
        );
        let im_rec = p.by(
            "eqtrd",
            &[
                &im_rec,
                &p.by(
                    "oveq1d",
                    &[&p.by("imcjd", &[&z], &[])],
                    &[("C", "( ( abs ` Z ) ^ 2 )"), ("F", "/")],
                ),
            ],
            &[],
        );
        // ( -u Im Z / K ) Im W = -u ( ( Im Z Im W ) / K ).
        let (im_zc, im_wc, size_c) = (
            p.by("recnd", &[&im_z], &[]),
            p.by("recnd", &[&im_w], &[]),
            p.by("recnd", &[&size_re], &[]),
        );
        let neg_out = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq1d",
                    &[&p.by(
                        "eqcomd",
                        &[&p.by("divnegd", &[&im_zc, &size_c, &size_nz], &[])],
                        &[],
                    )],
                    &[("C", "( Im ` W )"), ("F", "x.")],
                ),
                &p.by(
                    "mulneg1d",
                    &[&p.by("divcld", &[&im_zc, &size_c, &size_nz], &[]), &im_wc],
                    &[],
                ),
            ],
            &[],
        );
        let regroup = p.by(
            "negeqd",
            &[&p.by(
                "eqcomd",
                &[&p.by("div23d", &[&im_zc, &im_wc, &size_c, &size_nz], &[])],
                &[],
            )],
            &[],
        );
        let product = p.by(
            "eqtrd",
            &[
                &p.by("oveq1d", &[&im_rec], &[("C", "( Im ` W )"), ("F", "x.")]),
                &p.by("eqtrd", &[&neg_out, &regroup], &[]),
            ],
            &[],
        );
        let v_re = p.by(
            "redivcld",
            &[&p.by("remulcld", &[&im_z, &im_w], &[]), &size_re, &size_nz],
            &[],
        );
        let sides = p.by(
            "bitr4d",
            &[
                &p.by("breq1d", &[&product], &[("C", "0"), ("R", "<")]),
                &p.by("lt0neg2d", &[&v_re], &[]),
            ],
            &[],
        );
        let sides = p.by(
            "bitr4d",
            &[
                &sides,
                &p.by(
                    "gt0divd",
                    &[&p.by("remulcld", &[&im_z, &im_w], &[]), &size],
                    &[],
                ),
            ],
            &[],
        );
        let said = p.is(
            sides,
            &format!(
                "( {g} -> ( ( ( Im ` ( 1 / Z ) ) x. ( Im ` W ) ) < 0 <-> 0 < ( ( Im ` Z ) x. ( Im ` W ) ) ) )"
            ),
        );
        let text = statement(&p, &said);
        (said, text)
    };
    b.define(label, &text);
    Lemma::new(label, text, said.proof)
}

/// `gline`: the angles along a straight line, `angles-on-a-line`.
///
/// With R the vertex and S, P, Q, T in order, write u, a, b, c for S − R,
/// P − R, Q − R and T − R. The three angles are the arguments of a/u, b/a
/// and c/b, whose product is c/u, a negative real because R is between S
/// and T. That P and Q are on one side of the line puts a/u and b/u on one
/// side of the real line; that S and Q are on opposite sides of RP puts b/a
/// with a/u (`grecsgn`); and c/b is a negative multiple of u/b, which puts
/// it with b/u. So `gargsum` gives the sum of their sizes as π, which is
/// 180°.
fn along_a_line(b: &mut Builder) -> Lemma {
    let conjuncts = [
        "P e. CC",
        "Q e. CC",
        "R e. CC",
        "S e. CC",
        "T e. CC",
        "( S =/= R /\\ ( ( T - R ) / ( S - R ) ) e. RR /\\ ( ( T - R ) / ( S - R ) ) < 0 )",
        "0 < ( ( Im ` ( ( P - R ) / ( S - R ) ) ) x. ( Im ` ( ( Q - R ) / ( S - R ) ) ) )",
        "( ( Im ` ( ( S - R ) / ( P - R ) ) ) x. ( Im ` ( ( Q - R ) / ( P - R ) ) ) ) < 0",
    ];
    let label = "gline";
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&conjuncts);
        let h = p.parts(&conjuncts);
        let (pc, qc, rc, sc, tc) = (&h[0], &h[1], &h[2], &h[3], &h[4]);
        let (between, same, opp) = (&h[5], &h[6], &h[7]);
        let s_apart = p.by("simp1d", &[between], &[]);
        let t_re = p.by("simp2d", &[between], &[]);
        let t_neg = p.by("simp3d", &[between], &[]);
        let u = p.by("subcld", &[sc, rc], &[]);
        let un = p.by("subne0d", &[sc, rc, &s_apart], &[]);
        let a = p.by("subcld", &[pc, rc], &[]);
        let bq = p.by("subcld", &[qc, rc], &[]);
        let c = p.by("subcld", &[tc, rc], &[]);
        let alpha = p.by("divcld", &[&a, &u, &un], &[]);
        let beta = p.by("divcld", &[&bq, &u, &un], &[]);
        let (im_a, im_b) =
            (p.by("imcld", &[&alpha], &[]), p.by("imcld", &[&beta], &[]));
        // Neither a/u nor b/u is real, so a and b are not 0.
        let both = p.by(
            "mpbird",
            &[
                &p.by("gt0ne0d", &[same], &[]),
                &p.by(
                    "mulne0bd",
                    &[&p.by("recnd", &[&im_a], &[]), &p.by("recnd", &[&im_b], &[])],
                    &[],
                ),
            ],
            &[],
        );
        let alpha_n = p.nonzero(
            "( ( P - R ) / ( S - R ) )",
            &g,
            &p.by("simpld", &[&both], &[]),
        );
        let beta_n = p.nonzero(
            "( ( Q - R ) / ( S - R ) )",
            &g,
            &p.by("simprd", &[&both], &[]),
        );
        let an = p.by(
            "mpbird",
            &[&alpha_n, &p.by("divne0bd", &[&a, &u, &un], &[])],
            &[],
        );
        let bn = p.by(
            "mpbird",
            &[&beta_n, &p.by("divne0bd", &[&bq, &u, &un], &[])],
            &[],
        );
        let t_c = p.by("recnd", &[&t_re], &[]);
        let t_nz = p.by("lt0ne0d", &[&t_neg], &[]);
        let cn = p.by(
            "mpbird",
            &[&t_nz, &p.by("divne0bd", &[&c, &u, &un], &[])],
            &[],
        );
        let x2 = p.by("divcld", &[&bq, &a, &an], &[]);
        let x3 = p.by("divcld", &[&c, &bq, &bn], &[]);
        // The product of the three is c/u.
        let product = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq1d",
                    &[&p.by("dmdcand", &[&bq, &a, &u, &an, &un], &[])],
                    &[("C", "( ( T - R ) / ( Q - R ) )"), ("F", "x.")],
                ),
                &p.by("dmdcand", &[&c, &bq, &u, &bn, &un], &[]),
            ],
            &[],
        );
        let prod_re = p.by("eqeltrd", &[&product, &t_re], &[]);
        let prod_neg = p.by("eqbrtrd", &[&product, &t_neg], &[]);
        // b/a is on a/u's side: S and Q are on opposite sides of RP, and
        // (S − R)/(P − R) is 1/(a/u).
        let flip = p.by("recdivd", &[&a, &u, &an, &un], &[]);
        let with_x2 = p.by(
            "mpbid",
            &[
                &p.by(
                    "eqbrtrd",
                    &[
                        &p.by(
                            "oveq1d",
                            &[&p.by("fveq2d", &[&flip], &[("F", "Im")])],
                            &[("C", "( Im ` ( ( Q - R ) / ( P - R ) ) )"), ("F", "x.")],
                        ),
                        opp,
                    ],
                    &[],
                ),
                &p.apply(
                    "grecsgn",
                    &[&p.joined(&[&p.joined(&[&alpha, &alpha_n]), &x2])],
                    &[],
                ),
            ],
            &[],
        );
        // c/b is t (u/b), and u/b is 1/(b/u), on the other side from b/u.
        let c_is = p.by("eqcomd", &[&p.by("divcan1d", &[&c, &u, &un], &[])], &[]);
        let x3_is = p.by(
            "eqtrd",
            &[
                &p.by("oveq1d", &[&c_is], &[("C", "( Q - R )"), ("F", "/")]),
                &p.by("divassd", &[&t_c, &u, &bq, &bn], &[]),
            ],
            &[],
        );
        let x3_is = p.by(
            "eqtrd",
            &[
                &x3_is,
                &p.by(
                    "oveq2d",
                    &[&p.by(
                        "eqcomd",
                        &[&p.by("recdivd", &[&bq, &u, &bn, &un], &[])],
                        &[],
                    )],
                    &[("C", "( ( T - R ) / ( S - R ) )"), ("F", "x.")],
                ),
            ],
            &[],
        );
        let rb = p.by("reccld", &[&beta, &beta_n], &[]);
        let im_x3 = p.by(
            "eqtrd",
            &[
                &p.by("fveq2d", &[&x3_is], &[("F", "Im")]),
                &p.by("immul2d", &[&t_re, &rb], &[]),
            ],
            &[],
        );
        let im_rb = p.by("imcld", &[&rb], &[]);
        // Im(1/(b/u)) Im(a/u) < 0, from Im(a/u) Im(b/u) > 0.
        let same_turned = p.by(
            "breqtrd",
            &[
                same,
                &p.by(
                    "mulcomd",
                    &[&p.by("recnd", &[&im_a], &[]), &p.by("recnd", &[&im_b], &[])],
                    &[],
                ),
            ],
            &[],
        );
        let rb_a = p.by(
            "mpbird",
            &[
                &same_turned,
                &p.apply(
                    "grecsgn",
                    &[&p.joined(&[&p.joined(&[&beta, &beta_n]), &alpha])],
                    &[],
                ),
            ],
            &[],
        );
        let both_neg = p.apply(
            "mullt0",
            &[&p.joined(&[
                &p.joined(&[&t_re, &t_neg]),
                &p.joined(&[&p.by("remulcld", &[&im_rb, &im_a], &[]), &rb_a]),
            ])],
            &[],
        );
        let regroup = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq2d",
                    &[&im_x3],
                    &[("C", "( Im ` ( ( P - R ) / ( S - R ) ) )"), ("F", "x.")],
                ),
                &p.by(
                    "mul12d",
                    &[
                        &p.by("recnd", &[&im_a], &[]),
                        &t_c,
                        &p.by("recnd", &[&im_rb], &[]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let regroup = p.by(
            "eqtrd",
            &[
                &regroup,
                &p.by(
                    "oveq2d",
                    &[&p.by(
                        "mulcomd",
                        &[
                            &p.by("recnd", &[&im_a], &[]),
                            &p.by("recnd", &[&im_rb], &[]),
                        ],
                        &[],
                    )],
                    &[("C", "( ( T - R ) / ( S - R ) )"), ("F", "x.")],
                ),
            ],
            &[],
        );
        let with_x3 = p.by("breqtrrd", &[&both_neg, &regroup], &[]);
        let all =
            p.joined(&[&alpha, &x2, &x3, &with_x2, &with_x3, &prod_re, &prod_neg]);
        let sizes = p.apply("gargsum", &[&all], &[]);
        // The three angles are those arguments.
        let def = p.ang_defined();
        let angle = |x: (&Said, &Said, &str), y: (&Said, &Said, &str)| -> Said {
            let both = p.joined(&[&p.joined(&[x.0, x.1]), &p.joined(&[y.0, y.1])]);
            let value = p.by("angval", &[&def], &[("A", x.2), ("B", y.2)]);
            p.by(
                "fveq2d",
                &[&p.by("syl", &[&both, &value], &[])],
                &[("F", "abs")],
            )
        };
        let first = angle((&u, &un, "( S - R )"), (&a, &an, "( P - R )"));
        let second = angle((&a, &an, "( P - R )"), (&bq, &bn, "( Q - R )"));
        let third = p.by(
            "eqtrd",
            &[
                &p.apply(
                    "gangsym",
                    &[&p.joined(&[&p.joined(&[&c, &cn]), &p.joined(&[&bq, &bn])])],
                    &[],
                ),
                &angle((&bq, &bn, "( Q - R )"), (&c, &cn, "( T - R )")),
            ],
            &[],
        );
        let angles = p.by(
            "oveq12d",
            &[&p.by("oveq12d", &[&first, &second], &[("F", "+")]), &third],
            &[("F", "+")],
        );
        let pi = p.by("eqtrd", &[&angles, &sizes], &[]);
        // π is 180°: ( 180 x. π ) / 180.
        let n18 = p.by(
            "decnncl",
            &[&p.by("1nn0", &[], &[]), &p.by("8nn", &[], &[])],
            &[],
        );
        let n180 = p.always(&p.by("decnncl2", &[&n18], &[]), &g);
        let degrees = p.by(
            "divcan3d",
            &[
                &p.always(&p.by("picn", &[], &[]), &g),
                &p.by("nncnd", &[&n180], &[]),
                &p.by("nnne0d", &[&n180], &[]),
            ],
            &[],
        );
        let said = p.by("eqtr4d", &[&pi, &degrees], &[]);
        let said = p.is(
            said,
            &format!(
                "( {g} -> ( ( ( abs ` ( ( S - R ) ang ( P - R ) ) ) + ( abs ` ( ( P - R ) ang ( Q - R ) ) ) ) + ( abs ` ( ( T - R ) ang ( Q - R ) ) ) ) = ( ( ; ; 1 8 0 x. _pi ) / ; ; 1 8 0 ) )"
            ),
        );
        let said = p.curried(said, &conjuncts);
        let text = statement(&p, &said);
        (said, text)
    };
    b.define(label, &text);
    Lemma::new(label, text, said.proof)
}

/// What `parallel-through` says of D and E, as set.mm writes it.
fn through(d: &str, e: &str) -> String {
    format!(
        "( ( ( ( ( ( ( {d} - R ) / ( Q - P ) ) e. RR /\\ ( ( {e} - R ) / ( P - Q ) ) e. RR ) \
         /\\ ( {d} =/= R /\\ ( ( {e} - R ) / ( {d} - R ) ) e. RR /\\ ( ( {e} - R ) / ( {d} - R ) ) < 0 ) ) \
         /\\ ( ( Im ` ( ( {d} - R ) / ( P - R ) ) ) x. ( Im ` ( ( Q - R ) / ( P - R ) ) ) ) < 0 ) \
         /\\ ( ( Im ` ( ( {e} - R ) / ( Q - R ) ) ) x. ( Im ` ( ( P - R ) / ( Q - R ) ) ) ) < 0 ) \
         /\\ 0 < ( ( Im ` ( ( P - R ) / ( {d} - R ) ) ) x. ( Im ` ( ( Q - R ) / ( {d} - R ) ) ) ) )"
    )
}

/// `gparthru`: the parallel to PQ through R, `parallel-through`.
///
/// D is R + (P − Q) and E is R + (Q − P), so D − R and E − R are P − Q and
/// Q − P: each a multiple of the other and of Q − P, which is parallel and
/// between. Each side condition is then a sign of an imaginary part of a
/// quotient the triangle makes non-real: (P − R)/(P − Q) for P and Q's side
/// of RD, and (P − Q)/(P − R) and (Q − P)/(Q − R) for D's and E's sides of
/// RP and RQ, whose second factor is 1 minus the first.
fn parallel_through(b: &mut Builder) -> Lemma {
    let conjuncts = [
        "P e. CC",
        "Q e. CC",
        "R e. CC",
        "( ( ( -. P = Q /\\ -. Q = R ) /\\ -. P = R ) /\\ -. ( ( R - P ) / ( Q - P ) ) e. RR )",
    ];
    let (d0, e0) = ("( R + ( P - Q ) )", "( R + ( Q - P ) )");
    let label = "gparthru";
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&conjuncts);
        let h = p.parts(&conjuncts);
        let (pc, qc, rc) = (&h[0], &h[1], &h[2]);
        let tri = &h[3];
        let apart3 = p.by("simpld", &[tri], &[]);
        let not_real = p.by("simprd", &[tri], &[]);
        let pq = p.by(
            "neqned",
            &[&p.by("simpld", &[&p.by("simpld", &[&apart3], &[])], &[])],
            &[],
        );
        let qr = p.by(
            "neqned",
            &[&p.by("simprd", &[&p.by("simpld", &[&apart3], &[])], &[])],
            &[],
        );
        let pr = p.by("neqned", &[&p.by("simprd", &[&apart3], &[])], &[]);
        let diff = |x: &Said, y: &Said, apart: &Said| -> (Said, Said) {
            (
                p.by("subcld", &[x, y], &[]),
                p.by("subne0d", &[x, y, apart], &[]),
            )
        };
        let (pmq, pmq_n) = diff(pc, qc, &pq);
        let (qmp, qmp_n) = diff(qc, pc, &p.by("necomd", &[&pq], &[]));
        let (pmr, pmr_n) = diff(pc, rc, &pr);
        let (qmr, qmr_n) = diff(qc, rc, &qr);
        let (rmp, rmp_n) = diff(rc, pc, &p.by("necomd", &[&pr], &[]));
        let (rmq, rmq_n) = diff(rc, qc, &p.by("necomd", &[&qr], &[]));
        let dc = p.by("addcld", &[rc, &pmq], &[]);
        let ec = p.by("addcld", &[rc, &qmp], &[]);
        let dr = p.by("pncan2d", &[rc, &pmq], &[]);
        let er = p.by("pncan2d", &[rc, &qmp], &[]);
        let neg1 = p.always(&p.by("neg1rr", &[], &[]), &g);

        // Parallel: (D − R)/(Q − P) and (E − R)/(P − Q) are both −1.
        let par1 = p.by(
            "eqeltrd",
            &[
                &p.by(
                    "eqtrd",
                    &[
                        &p.by("oveq1d", &[&dr], &[("C", "( Q - P )"), ("F", "/")]),
                        &p.minus_one(qc, pc, &qmp_n),
                    ],
                    &[],
                ),
                &neg1,
            ],
            &[],
        );
        let par2 = p.by(
            "eqeltrd",
            &[
                &p.by(
                    "eqtrd",
                    &[
                        &p.by("oveq1d", &[&er], &[("C", "( P - Q )"), ("F", "/")]),
                        &p.minus_one(pc, qc, &pmq_n),
                    ],
                    &[],
                ),
                &neg1,
            ],
            &[],
        );
        // Between: D is not R, and (E − R)/(D − R) is −1.
        let d_apart = p.by(
            "subne0ad",
            &[&dc, rc, &p.by("eqnetrd", &[&dr, &pmq_n], &[])],
            &[],
        );
        let ratio = p.by(
            "eqtrd",
            &[
                &p.by("oveq12d", &[&er, &dr], &[("F", "/")]),
                &p.minus_one(pc, qc, &pmq_n),
            ],
            &[],
        );
        let between = p.by(
            "3jca",
            &[
                &d_apart,
                &p.by("eqeltrd", &[&ratio, &neg1], &[]),
                &p.by(
                    "eqbrtrd",
                    &[&ratio, &p.always(&p.by("neg1lt0", &[], &[]), &g)],
                    &[],
                ),
            ],
            &[],
        );
        // One of D, E against one side line: X − Y over X − R is w, the other
        // vertex Y − R over X − R is 1 − w, so the product is −(Im w)².
        let opposite = |x: &Said,
                        y: &Said,
                        xr: (&Said, &Said),
                        num: &Said,
                        w_eq: &Said,
                        w_not_real: &Said|
         -> Said {
            let (xmr, xmr_n) = xr;
            let xmy = p.by("subcld", &[x, y], &[]);
            let below = p.show(&xmr.says.children()[1].children()[0]);
            let first = p.by("oveq1d", &[num], &[("C", &below), ("F", "/")]);
            let w = p.by("divcld", &[&xmy, xmr, xmr_n], &[]);
            let im_w = p.by("imcld", &[&w], &[]);
            let im_w_n = p.off_line(&w, w_eq, w_not_real);
            // (Y − R)/(X − R) = −w + 1.
            let split = p.by("eqcomd", &[&p.by("npncand", &[y, x, rc], &[])], &[]);
            let ymx = p.by("subcld", &[y, x], &[]);
            let second = p.by(
                "eqtrd",
                &[
                    &p.by("oveq1d", &[&split], &[("C", &below), ("F", "/")]),
                    &p.by("divdird", &[&ymx, xmr, xmr, xmr_n], &[]),
                ],
                &[],
            );
            let neg_w = p.by(
                "eqtrd",
                &[
                    &p.by(
                        "oveq1d",
                        &[&p.by("eqcomd", &[&p.by("negsubdi2d", &[x, y], &[])], &[])],
                        &[("C", &below), ("F", "/")],
                    ),
                    &p.by("eqcomd", &[&p.by("divnegd", &[&xmy, xmr, xmr_n], &[])], &[]),
                ],
                &[],
            );
            let second = p.by(
                "eqtrd",
                &[
                    &second,
                    &p.by(
                        "oveq12d",
                        &[&neg_w, &p.by("dividd", &[xmr, xmr_n], &[])],
                        &[("F", "+")],
                    ),
                ],
                &[],
            );
            let one = p.always(&p.by("ax-1cn", &[], &[]), &g);
            let im_second = p.by(
                "eqtrd",
                &[
                    &p.by("fveq2d", &[&second], &[("F", "Im")]),
                    &p.by("imaddd", &[&p.by("negcld", &[&w], &[]), &one], &[]),
                ],
                &[],
            );
            let im_second = p.by(
                "eqtrd",
                &[
                    &im_second,
                    &p.by(
                        "oveq12d",
                        &[
                            &p.by("imnegd", &[&w], &[]),
                            &p.always(&p.by("im1", &[], &[]), &g),
                        ],
                        &[("F", "+")],
                    ),
                ],
                &[],
            );
            let im_second = p.by(
                "eqtrd",
                &[
                    &im_second,
                    &p.by(
                        "addridd",
                        &[&p.by("negcld", &[&p.by("recnd", &[&im_w], &[])], &[])],
                        &[],
                    ),
                ],
                &[],
            );
            let product = p.by(
                "eqtrd",
                &[
                    &p.by(
                        "oveq12d",
                        &[&p.by("fveq2d", &[&first], &[("F", "Im")]), &im_second],
                        &[("F", "x.")],
                    ),
                    &p.by(
                        "mulneg2d",
                        &[&p.by("recnd", &[&im_w], &[]), &p.by("recnd", &[&im_w], &[])],
                        &[],
                    ),
                ],
                &[],
            );
            let square = p.by("msqgt0d", &[&im_w, &im_w_n], &[]);
            let negative = p.by(
                "mpbid",
                &[
                    &square,
                    &p.by("lt0neg2d", &[&p.by("remulcld", &[&im_w, &im_w], &[])], &[]),
                ],
                &[],
            );
            p.by("eqbrtrd", &[&product, &negative], &[])
        };
        // (P − Q)/(P − R) is (Q − P)/(R − P), off the line by `gtrirec`.
        let w1_eq = p.by(
            "eqtr3d",
            &[
                &p.by(
                    "oveq12d",
                    &[
                        &p.by("negsubdi2d", &[qc, pc], &[]),
                        &p.by("negsubdi2d", &[rc, pc], &[]),
                    ],
                    &[("F", "/")],
                ),
                &p.by("div2negd", &[&qmp, &rmp, &rmp_n], &[]),
            ],
            &[],
        );
        let w1_not = p.by(
            "mtod",
            &[
                &not_real,
                &p.apply(
                    "gtrirec",
                    &[&p.joined(&[
                        &p.joined(&[&qmp, &qmp_n]),
                        &p.joined(&[&rmp, &rmp_n]),
                    ])],
                    &[],
                ),
            ],
            &[],
        );
        let opp1 = opposite(pc, qc, (&pmr, &pmr_n), &dr, &w1_eq, &w1_not);
        // (Q − P)/(Q − R) is (P − Q)/(R − Q), off the line by `gtricol`.
        let w2_eq = p.by(
            "eqtr3d",
            &[
                &p.by(
                    "oveq12d",
                    &[
                        &p.by("negsubdi2d", &[pc, qc], &[]),
                        &p.by("negsubdi2d", &[rc, qc], &[]),
                    ],
                    &[("F", "/")],
                ),
                &p.by("div2negd", &[&pmq, &rmq, &rmq_n], &[]),
            ],
            &[],
        );
        let w2_not = p.by(
            "mtod",
            &[
                &not_real,
                &p.apply(
                    "gtricol",
                    &[&p.joined(&[
                        &p.by("3jca", &[pc, qc, rc], &[]),
                        &p.joined(&[&pmq_n, &rmq_n]),
                    ])],
                    &[],
                ),
            ],
            &[],
        );
        let opp2 = opposite(qc, pc, (&qmr, &qmr_n), &er, &w2_eq, &w2_not);
        // P and Q on one side of RD: (Q − R)/(P − Q) is −1 + (P − R)/(P − Q).
        let z = p.by("divcld", &[&pmr, &pmq, &pmq_n], &[]);
        let im_z = p.by("imcld", &[&z], &[]);
        let z_eq = p.by(
            "eqtr3d",
            &[
                &p.by(
                    "oveq12d",
                    &[
                        &p.by("negsubdi2d", &[rc, pc], &[]),
                        &p.by("negsubdi2d", &[qc, pc], &[]),
                    ],
                    &[("F", "/")],
                ),
                &p.by("div2negd", &[&rmp, &qmp, &qmp_n], &[]),
            ],
            &[],
        );
        let im_z_n = p.off_line(&z, &z_eq, &not_real);
        let first = p.by("oveq2d", &[&dr], &[("C", "( P - R )"), ("F", "/")]);
        let split = p.by("eqcomd", &[&p.by("npncand", &[qc, pc, rc], &[])], &[]);
        let second = p.by(
            "eqtrd",
            &[
                &p.by("oveq2d", &[&dr], &[("C", "( Q - R )"), ("F", "/")]),
                &p.by("oveq1d", &[&split], &[("C", "( P - Q )"), ("F", "/")]),
            ],
            &[],
        );
        let second = p.by(
            "eqtrd",
            &[&second, &p.by("divdird", &[&qmp, &pmr, &pmq, &pmq_n], &[])],
            &[],
        );
        let second = p.by(
            "eqtrd",
            &[
                &second,
                &p.by(
                    "oveq1d",
                    &[&p.minus_one(pc, qc, &pmq_n)],
                    &[("C", "( ( P - R ) / ( P - Q ) )"), ("F", "+")],
                ),
            ],
            &[],
        );
        let neg1c = p.by("recnd", &[&neg1], &[]);
        let im_second = p.by(
            "eqtrd",
            &[
                &p.by("fveq2d", &[&second], &[("F", "Im")]),
                &p.by("imaddd", &[&neg1c, &z], &[]),
            ],
            &[],
        );
        let im_second = p.by(
            "eqtrd",
            &[
                &im_second,
                &p.by(
                    "eqtrd",
                    &[
                        &p.by(
                            "oveq1d",
                            &[&p.by("reim0d", &[&neg1], &[])],
                            &[("C", "( Im ` ( ( P - R ) / ( P - Q ) ) )"), ("F", "+")],
                        ),
                        &p.by("addlidd", &[&p.by("recnd", &[&im_z], &[])], &[]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let product = p.by(
            "oveq12d",
            &[&p.by("fveq2d", &[&first], &[("F", "Im")]), &im_second],
            &[("F", "x.")],
        );
        let same_side = p.by(
            "breqtrrd",
            &[&p.by("msqgt0d", &[&im_z, &im_z_n], &[]), &product],
            &[],
        );

        let body = p.joined(&[&par1, &par2, &between, &opp1, &opp2, &same_side]);
        let body = p.is(body, &format!("( {g} -> {} )", through(d0, e0)));
        // There are such D and E: these.
        let y_is = format!("y = {e0}");
        let y_eq = p.by("simpr", &[], &[("ph", &g), ("ps", &y_is)]);
        let swap_y = p
            .cong(
                &y_eq,
                &p.term("y", "class"),
                &p.term(&through(d0, "y"), "wff"),
            )
            .expect("the claim names y");
        let inner = p.by("rspcedvd", &[&ec, &swap_y, &body], &[]);
        let x_is = format!("x = {d0}");
        let x_eq = p.by("simpr", &[], &[("ph", &g), ("ps", &x_is)]);
        let swap_x = p
            .cong(
                &x_eq,
                &p.term("x", "class"),
                &p.term(&through("x", "y"), "wff"),
            )
            .expect("the claim names x");
        let swap_x = p.by("rexbidv", &[&swap_x], &[("x", "y"), ("A", "CC")]);
        let said = p.by("rspcedvd", &[&dc, &swap_x, &inner], &[]);
        let said = p.curried(said, &conjuncts);
        let text = statement(&p, &said);
        (said, text)
    };
    b.define(label, &text);
    Lemma::new(label, text, said.proof)
}

/// Each parallels lemma, in the order a later one may take an earlier.
pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![
        arm_scaled(b),
        alternate(b),
        arguments_positive(b),
        arguments_sum(b),
        reciprocal_side(b),
        along_a_line(b),
        parallel_through(b),
    ]
}

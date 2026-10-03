//! Similar triangles and the right triangle, for `proved.mm`.
//!
//! Pythagoras is proved as a school text proves it: drop the altitude from
//! the right angle, and the two triangles it makes are each similar to the
//! whole. Similarity is a theorem of the readable layer, from the angle sum
//! and the law of sines; what it and the proof cite of the plane is here.
//! A distance is real, a point between two others is between them read
//! either way, lies on the ray from either end through the other, and
//! divides the distance between them; the sine of an angle of a triangle is
//! positive; the law of sines; and the foot of the altitude from a right
//! angle.
//!
//! Each is a fact about differences of complex numbers. A point S between P
//! and Q is one where (Q − S)/(P − S) is a negative real q, so that Q − S is
//! q(P − S): most of what follows is that equation read one way or another.

use crate::mm::Builder;
use crate::proofs::Lemma;

use super::parallels::{statement, Prover, Said};

pub const HEAD: &str =
    "$( Triangles: similar triangles and the right triangle, as Pythagoras asks
   of them. $)

$( `angval` reads a value of the angle by substituting for the two names
   `df-ang` binds, and asks that they be free of what is substituted. $)
$d x y $.
$d x P $.  $d y P $.
$d x Q $.  $d y Q $.
$d x R $.  $d y R $.
$d x S $.  $d y S $.
$d x T $.  $d y T $.

";

/// R is between S and T, as the `between` notation writes it.
fn between(r: &str, s: &str, t: &str) -> String {
    format!(
        "( {s} =/= {r} /\\ ( ( {t} - {r} ) / ( {s} - {r} ) ) e. RR /\\ ( ( {t} - {r} ) / ( {s} - {r} ) ) < 0 )"
    )
}

/// Register a lemma proved as `said` under `label`, and give it back.
fn finish(b: &mut Builder, label: &str, said: Said, text: String) -> Lemma {
    b.define(label, &text);
    Lemma::new(label, text, said.proof)
}

/// What the parts of S being between P and Q give, under the antecedent:
/// P − S, not 0; q = (Q − S)/(P − S), real and negative; and Q − S = q(P − S).
struct Between {
    w: Said,
    q_real: Said,
    q_below: Said,
    q_number: Said,
    along: Said,
}

impl Prover<'_> {
    /// S between P and Q, read as an equation: `cc` holds P, Q and S as
    /// numbers and `bet` the between, all under one antecedent.
    fn between_parts(&self, p: &Said, q: &Said, s: &Said, bet: &Said) -> Between {
        let apart = self.by("simp1d", &[bet], &[]);
        let q_real = self.by("simp2d", &[bet], &[]);
        let q_below = self.by("simp3d", &[bet], &[]);
        let w = self.by("subcld", &[p, s], &[]);
        let w_apart = self.by("subne0d", &[p, s, &apart], &[]);
        let q_number = self.by("recnd", &[&q_real], &[]);
        let qs = self.by("subcld", &[q, s], &[]);
        let along = self.by(
            "eqcomd",
            &[&self.by("divcan1d", &[&qs, &w, &w_apart], &[])],
            &[],
        );
        Between {
            w,
            q_real,
            q_below,
            q_number,
            along,
        }
    }
}

/// `gdistre`: a distance is a real number, `distance-real`.
fn distance_real(b: &mut Builder) -> Lemma {
    let conjuncts = ["P e. CC", "Q e. CC"];
    let (said, text) = {
        let p = Prover { b };
        let h = p.parts(&conjuncts);
        let said = p.by("abscld", &[&p.by("subcld", &[&h[0], &h[1]], &[])], &[]);
        let said = p.curried(said, &conjuncts);
        let text = statement(&p, &said);
        (said, text)
    };
    finish(b, "gdistre", said, text)
}

/// `gbetsym`: between S and T is between T and S, `between-symmetric`.
///
/// (S − R)/(T − R) is the reciprocal of (T − R)/(S − R), and the reciprocal
/// of a negative real is a negative real; T is not R, since the quotient is
/// not 0.
fn between_turned(b: &mut Builder) -> Lemma {
    let conjuncts = ["R e. CC", "S e. CC", "T e. CC", &between("R", "S", "T")];
    let conjuncts: Vec<&str> = conjuncts.iter().map(|s| s.as_ref()).collect();
    let (said, text) = {
        let p = Prover { b };
        let h = p.parts(&conjuncts);
        let (rc, sc, tc, bet) = (&h[0], &h[1], &h[2], &h[3]);
        let s_apart = p.by("simp1d", &[bet], &[]);
        let q_real = p.by("simp2d", &[bet], &[]);
        let q_below = p.by("simp3d", &[bet], &[]);
        let u = p.by("subcld", &[sc, rc], &[]);
        let u_apart = p.by("subne0d", &[sc, rc, &s_apart], &[]);
        let v = p.by("subcld", &[tc, rc], &[]);
        let q_apart = p.by("lt0ne0d", &[&q_below], &[]);
        let v_apart = p.by(
            "mpbird",
            &[&q_apart, &p.by("divne0bd", &[&v, &u, &u_apart], &[])],
            &[],
        );
        let t_apart = p.by("subne0ad", &[tc, rc, &v_apart], &[]);
        let flip = p.by(
            "eqcomd",
            &[&p.by("recdivd", &[&v, &u, &v_apart, &u_apart], &[])],
            &[],
        );
        let inv_real = p.by("rereccld", &[&q_real, &q_apart], &[]);
        let inv_below = p.by(
            "mpbid",
            &[&q_below, &p.by("reclt0", &[&q_real, &q_apart], &[])],
            &[],
        );
        let said = p.by(
            "3jca",
            &[
                &t_apart,
                &p.by("eqeltrd", &[&flip, &inv_real], &[]),
                &p.by("eqbrtrd", &[&flip, &inv_below], &[]),
            ],
            &[],
        );
        let said = p.curried(said, &conjuncts);
        let text = statement(&p, &said);
        (said, text)
    };
    finish(b, "gbetsym", said, text)
}

/// `gangseg`: an angle measured along a segment, `angle-along-segment`.
///
/// With S between P and Q and q as above, Q − P is (1 − q)(S − P), and 1 − q
/// is positive, so S − P is a positive multiple of Q − P and the angle at P
/// is the same to either (`gangrp`).
fn along_segment(b: &mut Builder) -> Lemma {
    let bet = between("S", "P", "Q");
    let conjuncts = ["P e. CC", "Q e. CC", "R e. CC", "S e. CC", &bet, "-. R = P"];
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&conjuncts);
        let h = p.parts(&conjuncts);
        let (pc, qc, rc, sc) = (&h[0], &h[1], &h[2], &h[3]);
        let bw = p.between_parts(pc, qc, sc, &h[4]);
        let u = p.by("subcld", &[sc, pc], &[]);
        let u_apart = p.by(
            "subne0d",
            &[
                sc,
                pc,
                &p.by("necomd", &[&p.by("simp1d", &[&h[4]], &[])], &[]),
            ],
            &[],
        );
        // Q − S = −(q u), so Q − P = (Q − S) + u = u − q u = (1 − q) u.
        let qu = p.by("mulcld", &[&bw.q_number, &u], &[]);
        let negated = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq2d",
                    &[&p.by("eqcomd", &[&p.by("negsubdi2d", &[sc, pc], &[])], &[])],
                    &[("C", "( ( Q - S ) / ( P - S ) )"), ("F", "x.")],
                ),
                &p.by("mulneg2d", &[&bw.q_number, &u], &[]),
            ],
            &[],
        );
        let qs = p.by("eqtrd", &[&bw.along, &negated], &[]);
        let qp = p.by(
            "eqtr3d",
            &[
                &p.by("npncand", &[qc, sc, pc], &[]),
                &p.by("oveq1d", &[&qs], &[("C", "( S - P )"), ("F", "+")]),
            ],
            &[],
        );
        let qp = p.by(
            "eqtrd",
            &[
                &qp,
                &p.by(
                    "eqtrd",
                    &[
                        &p.by("addcomd", &[&p.by("negcld", &[&qu], &[]), &u], &[]),
                        &p.by("negsubd", &[&u, &qu], &[]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let one = p.always(&p.by("ax-1cn", &[], &[]), &g);
        let factor = p.by(
            "eqtrd",
            &[
                &p.by("subdird", &[&one, &bw.q_number, &u], &[]),
                &p.by(
                    "oveq1d",
                    &[&p.by("mullidd", &[&u], &[])],
                    &[
                        ("C", "( ( ( Q - S ) / ( P - S ) ) x. ( S - P ) )"),
                        ("F", "-"),
                    ],
                ),
            ],
            &[],
        );
        let qp = p.by("eqtr4d", &[&qp, &factor], &[]);
        // 1 − q is positive, so 1/(1 − q) is.
        let one_re = p.always(&p.by("1re", &[], &[]), &g);
        let zero_re = p.always(&p.by("0re", &[], &[]), &g);
        let oq_re = p.by("resubcld", &[&one_re, &bw.q_real], &[]);
        let below_one = p.by(
            "lttrd",
            &[
                &bw.q_real,
                &zero_re,
                &one_re,
                &bw.q_below,
                &p.always(&p.by("0lt1", &[], &[]), &g),
            ],
            &[],
        );
        let oq_pos = p.by(
            "mpbid",
            &[&below_one, &p.by("posdifd", &[&bw.q_real, &one_re], &[])],
            &[],
        );
        let oq_rp = p.by("elrpd", &[&oq_re, &oq_pos], &[]);
        let oq_c = p.by("rpcnd", &[&oq_rp], &[]);
        let oq_apart = p.by("rpne0d", &[&oq_rp], &[]);
        let lambda = p.by("rpreccld", &[&oq_rp], &[]);
        // S − P = (Q − P)/(1 − q) = (1/(1 − q))(Q − P).
        let qpc = p.by("subcld", &[qc, pc], &[]);
        let u_is = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq1d",
                    &[&qp],
                    &[("C", "( 1 - ( ( Q - S ) / ( P - S ) ) )"), ("F", "/")],
                ),
                &p.by("divcan3d", &[&u, &oq_c, &oq_apart], &[]),
            ],
            &[],
        );
        let u_is = p.by(
            "eqtr3d",
            &[&u_is, &p.by("divrec2d", &[&qpc, &oq_c, &oq_apart], &[])],
            &[],
        );
        let qp_apart = p.by(
            "eqnetrd",
            &[
                &qp,
                &p.by("mulne0d", &[&oq_c, &u, &oq_apart, &u_apart], &[]),
            ],
            &[],
        );
        let rpc = p.by("subcld", &[rc, pc], &[]);
        let rp_apart = p.by("subne0d", &[rc, pc, &p.by("neqned", &[&h[5]], &[])], &[]);
        let scaled = p.apply(
            "gangrp",
            &[&p.joined(&[
                &p.joined(&[
                    &p.joined(&[&qpc, &qp_apart]),
                    &p.joined(&[&rpc, &rp_apart]),
                ]),
                &lambda,
            ])],
            &[],
        );
        let at_p = p.by(
            "eqtrd",
            &[
                &p.by("oveq1d", &[&u_is], &[("C", "( R - P )"), ("F", "ang")]),
                &scaled,
            ],
            &[],
        );
        let said = p.by("fveq2d", &[&at_p], &[("F", "abs")]);
        let said = p.is(
            said,
            &format!(
                "( {g} -> ( abs ` ( ( S - P ) ang ( R - P ) ) ) = ( abs ` ( ( Q - P ) ang ( R - P ) ) ) )"
            ),
        );
        let said = p.curried(said, &conjuncts);
        let text = statement(&p, &said);
        (said, text)
    };
    finish(b, "gangseg", said, text)
}

/// `gsegadd`: the two parts of a segment add to it, `segment-addition`.
///
/// With w = P − S, Q − S is q w, so |SQ| is −q|w|, and P − Q is (1 − q) w,
/// so |PQ| is (1 − q)|w|, which is |w| + (−q)|w|.
fn segment_sum(b: &mut Builder) -> Lemma {
    let bet = between("S", "P", "Q");
    let conjuncts = ["P e. CC", "Q e. CC", "S e. CC", &bet];
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&conjuncts);
        let h = p.parts(&conjuncts);
        let (pc, qc, sc) = (&h[0], &h[1], &h[2]);
        let bw = p.between_parts(pc, qc, sc, &h[3]);
        let zero_re = p.always(&p.by("0re", &[], &[]), &g);
        let one = p.always(&p.by("ax-1cn", &[], &[]), &g);
        let one_re = p.always(&p.by("1re", &[], &[]), &g);
        let size_w = p.by("abscld", &[&bw.w], &[]);
        let size_wc = p.by("recnd", &[&size_w], &[]);
        // |SQ| = |q w| = (−q)|w|.
        let q_size = p.by(
            "absnidd",
            &[
                &bw.q_real,
                &p.by("ltled", &[&bw.q_real, &zero_re, &bw.q_below], &[]),
            ],
            &[],
        );
        let sq = p.by(
            "eqtrd",
            &[
                &p.by("abssubd", &[sc, qc], &[]),
                &p.by("fveq2d", &[&bw.along], &[("F", "abs")]),
            ],
            &[],
        );
        let sq = p.by(
            "eqtrd",
            &[
                &sq,
                &p.by(
                    "eqtrd",
                    &[
                        &p.by("absmuld", &[&bw.q_number, &bw.w], &[]),
                        &p.by(
                            "oveq1d",
                            &[&q_size],
                            &[("C", "( abs ` ( P - S ) )"), ("F", "x.")],
                        ),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        // P − Q = (P − S) − (Q − S) = w − q w = (1 − q) w.
        let pq = p.by(
            "eqtr3d",
            &[
                &p.by("nnncan2d", &[pc, qc, sc], &[]),
                &p.by("oveq2d", &[&bw.along], &[("C", "( P - S )"), ("F", "-")]),
            ],
            &[],
        );
        let factor = p.by(
            "eqtrd",
            &[
                &p.by("subdird", &[&one, &bw.q_number, &bw.w], &[]),
                &p.by(
                    "oveq1d",
                    &[&p.by("mullidd", &[&bw.w], &[])],
                    &[
                        ("C", "( ( ( Q - S ) / ( P - S ) ) x. ( P - S ) )"),
                        ("F", "-"),
                    ],
                ),
            ],
            &[],
        );
        let pq = p.by("eqtr4d", &[&pq, &factor], &[]);
        // |PQ| = (1 − q)|w|, since 1 − q is positive.
        let oq_re = p.by("resubcld", &[&one_re, &bw.q_real], &[]);
        let below_one = p.by(
            "lttrd",
            &[
                &bw.q_real,
                &zero_re,
                &one_re,
                &bw.q_below,
                &p.always(&p.by("0lt1", &[], &[]), &g),
            ],
            &[],
        );
        let oq_pos = p.by(
            "mpbid",
            &[&below_one, &p.by("posdifd", &[&bw.q_real, &one_re], &[])],
            &[],
        );
        let oq_c = p.by("recnd", &[&oq_re], &[]);
        let size_pq = p.by(
            "eqtrd",
            &[
                &p.by("fveq2d", &[&pq], &[("F", "abs")]),
                &p.by("absmuld", &[&oq_c, &bw.w], &[]),
            ],
            &[],
        );
        let size_pq = p.by(
            "eqtrd",
            &[
                &size_pq,
                &p.by(
                    "oveq1d",
                    &[&p.by(
                        "absidd",
                        &[&oq_re, &p.by("ltled", &[&zero_re, &oq_re, &oq_pos], &[])],
                        &[],
                    )],
                    &[("C", "( abs ` ( P - S ) )"), ("F", "x.")],
                ),
            ],
            &[],
        );
        // (1 − q)|w| = (1 + −q)|w| = |w| + (−q)|w|.
        let nq = p.by("negcld", &[&bw.q_number], &[]);
        let spread = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq1d",
                    &[&p.by(
                        "eqcomd",
                        &[&p.by("negsubd", &[&one, &bw.q_number], &[])],
                        &[],
                    )],
                    &[("C", "( abs ` ( P - S ) )"), ("F", "x.")],
                ),
                &p.by("adddird", &[&one, &nq, &size_wc], &[]),
            ],
            &[],
        );
        let spread = p.by(
            "eqtrd",
            &[
                &spread,
                &p.by(
                    "oveq1d",
                    &[&p.by("mullidd", &[&size_wc], &[])],
                    &[
                        (
                            "C",
                            "( -u ( ( Q - S ) / ( P - S ) ) x. ( abs ` ( P - S ) ) )",
                        ),
                        ("F", "+"),
                    ],
                ),
            ],
            &[],
        );
        let total = p.by("eqtrd", &[&size_pq, &spread], &[]);
        let said = p.by(
            "eqtr4d",
            &[
                &p.by(
                    "oveq2d",
                    &[&sq],
                    &[("C", "( abs ` ( P - S ) )"), ("F", "+")],
                ),
                &total,
            ],
            &[],
        );
        let said = p.is(
            said,
            &format!(
                "( {g} -> ( ( abs ` ( P - S ) ) + ( abs ` ( S - Q ) ) ) = ( abs ` ( P - Q ) ) )"
            ),
        );
        let said = p.curried(said, &conjuncts);
        let text = statement(&p, &said);
        (said, text)
    };
    finish(b, "gsegadd", said, text)
}

/// The three points of a triangle apart, as differences that are not 0:
/// what P, Q, R forming a triangle says before it says they are not on a
/// line, read off under one antecedent.
struct Apart {
    pq: Said,
    qr: Said,
    pr: Said,
}

impl Prover<'_> {
    fn apart(&self, tri: &Said) -> Apart {
        let three = self.by("simpld", &[tri], &[]);
        let two = self.by("simpld", &[&three], &[]);
        Apart {
            pq: self.by("neqned", &[&self.by("simpld", &[&two], &[])], &[]),
            qr: self.by("neqned", &[&self.by("simprd", &[&two], &[])], &[]),
            pr: self.by("neqned", &[&self.by("simprd", &[&three], &[])], &[]),
        }
    }
}

/// `gsinabs`: between −π and π, the sine of the size of an angle is the
/// size of its sine.
///
/// For a negative angle the size is its negation, whose sine is the
/// negated sine (`sinneg`); on [0, π] the sine is not negative
/// (`sinq12ge0`), so either way it is the size of the sine.
fn sine_of_size(b: &mut Builder) -> Lemma {
    let conjuncts = ["A e. RR", "-u _pi <_ A", "A <_ _pi"];
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&conjuncts);
        let h = p.parts(&conjuncts);
        let (a_re, low, high) = (&h[0], &h[1], &h[2]);
        let zero_re = p.always(&p.by("0re", &[], &[]), &g);
        let pi_re = p.always(&p.by("pire", &[], &[]), &g);
        let sides = p.apply("lelttric", &[&p.joined(&[&zero_re, a_re])], &[]);
        // 0 <_ A: the size is A, and so is the sine's.
        let up = {
            let side = "0 <_ A";
            let l = |s: &Said| p.lift(s, side);
            let ge = p.by("simpr", &[], &[("ph", &g), ("ps", side)]);
            let within = p.by(
                "mpbird",
                &[
                    &p.by("3jca", &[&l(a_re), &ge, &l(high)], &[]),
                    &p.apply(
                        "elicc2",
                        &[&p.joined(&[&l(&zero_re), &l(&pi_re)])],
                        &[("C", "A")],
                    ),
                ],
                &[],
            );
            let sine_ge = p.apply("sinq12ge0", &[&within], &[]);
            let sine_re = p.by("resincld", &[&l(a_re)], &[]);
            let size = p.by("absidd", &[&l(a_re), &ge], &[]);
            p.by(
                "eqtr4d",
                &[
                    &p.by("fveq2d", &[&size], &[("F", "sin")]),
                    &p.by("absidd", &[&sine_re, &sine_ge], &[]),
                ],
                &[],
            )
        };
        // A < 0: the size is −A, whose sine is −sin A, not negative.
        let down = {
            let side = "A < 0";
            let l = |s: &Said| p.lift(s, side);
            let lt = p.by("simpr", &[], &[("ph", &g), ("ps", side)]);
            let neg_re = p.by("renegcld", &[&l(a_re)], &[]);
            let neg_ge = p.by(
                "ltled",
                &[
                    &l(&zero_re),
                    &neg_re,
                    &p.by("mpbid", &[&lt, &p.by("lt0neg1d", &[&l(a_re)], &[])], &[]),
                ],
                &[],
            );
            let neg_le = p.by("lenegcon1d", &[&l(&pi_re), &l(a_re), &l(low)], &[]);
            let within = p.by(
                "mpbird",
                &[
                    &p.by("3jca", &[&neg_re, &neg_ge, &neg_le], &[]),
                    &p.apply(
                        "elicc2",
                        &[&p.joined(&[&l(&zero_re), &l(&pi_re)])],
                        &[("C", "-u A")],
                    ),
                ],
                &[],
            );
            let sine_ge = p.apply("sinq12ge0", &[&within], &[]);
            let flip = p.apply("sinneg", &[&p.by("recnd", &[&l(a_re)], &[])], &[]);
            let sine_re = p.by("resincld", &[&l(a_re)], &[]);
            let sine_le = p.by(
                "mpbird",
                &[
                    &p.by("breqtrd", &[&sine_ge, &flip], &[]),
                    &p.by("le0neg1d", &[&sine_re], &[]),
                ],
                &[],
            );
            let size = p.by(
                "absnidd",
                &[
                    &l(a_re),
                    &p.by("ltled", &[&l(a_re), &l(&zero_re), &lt], &[]),
                ],
                &[],
            );
            p.by(
                "eqtr4d",
                &[
                    &p.by(
                        "eqtrd",
                        &[&p.by("fveq2d", &[&size], &[("F", "sin")]), &flip],
                        &[],
                    ),
                    &p.by("absnidd", &[&sine_re, &sine_le], &[]),
                ],
                &[],
            )
        };
        let said = p.by("mpjaodan", &[&up, &down, &sides], &[]);
        let said = p.is(
            said,
            &format!("( {g} -> ( sin ` ( abs ` A ) ) = ( abs ` ( sin ` A ) ) )"),
        );
        let text = statement(&p, &said);
        (said, text)
    };
    finish(b, "gsinabs", said, text)
}

/// `gsinpos`: the sine of an angle of a triangle is positive,
/// `sine-positive`.
///
/// The angle at Q is the argument of (R − Q)/(P − Q), which is off the real
/// line because the three are not on one line (`gtricol`, `gtrirec`). Its
/// argument is then in (0, π) or (−π, 0), and its size in (0, π), where the
/// sine is positive (`sinq12gt0`).
fn sine_positive(b: &mut Builder) -> Lemma {
    let tri = "( ( ( -. P = Q /\\ -. Q = R ) /\\ -. P = R ) /\\ -. ( ( R - P ) / ( Q - P ) ) e. RR )";
    let conjuncts = ["P e. CC", "Q e. CC", "R e. CC", tri];
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&conjuncts);
        let h = p.parts(&conjuncts);
        let (pc, qc, rc) = (&h[0], &h[1], &h[2]);
        let ap = p.apart(&h[3]);
        let not_line = p.by("simprd", &[&h[3]], &[]);
        let x = p.by("subcld", &[pc, qc], &[]);
        let xn = p.by("subne0d", &[pc, qc, &ap.pq], &[]);
        let y = p.by("subcld", &[rc, qc], &[]);
        let yn = p.by("subne0d", &[rc, qc, &p.by("necomd", &[&ap.qr], &[])], &[]);
        // (P − Q)/(R − Q) is not real, nor its reciprocal z.
        let other = p.by(
            "mtod",
            &[
                &not_line,
                &p.apply(
                    "gtricol",
                    &[&p.joined(&[
                        &p.by("3jca", &[pc, qc, rc], &[]),
                        &p.joined(&[&xn, &yn]),
                    ])],
                    &[],
                ),
            ],
            &[],
        );
        let z_not = p.by(
            "mtod",
            &[
                &other,
                &p.apply(
                    "gtrirec",
                    &[&p.joined(&[&p.joined(&[&y, &yn]), &p.joined(&[&x, &xn])])],
                    &[],
                ),
            ],
            &[],
        );
        let z = p.by("divcld", &[&y, &x, &xn], &[]);
        let z_text = "( ( R - Q ) / ( P - Q ) )";
        let im_apart = p.off_line(
            &z,
            &p.by("eqidd", &[], &[("ph", &g), ("A", z_text)]),
            &z_not,
        );
        let im_re = p.by("imcld", &[&z], &[]);
        let zero_re = p.always(&p.by("0re", &[], &[]), &g);
        let pi_re = p.always(&p.by("pire", &[], &[]), &g);
        let sides = p.by(
            "mpbid",
            &[&im_apart, &p.by("lttri2d", &[&im_re, &zero_re], &[])],
            &[],
        );
        let theta = format!("( Im ` ( log ` {z_text} ) )");
        let pi_xr = p.by("rexrd", &[&pi_re], &[]);
        // Above the line: the argument is in (0, π) and is its own size.
        let up = {
            let side = "0 < ( Im ` ( ( R - Q ) / ( P - Q ) ) )";
            let l = |s: &Said| p.lift(s, side);
            let pos = p.by("simpr", &[], &[("ph", &g), ("ps", side)]);
            let arg = p.apply("argimgt0", &[&p.joined(&[&l(&z), &pos])], &[]);
            let arg_re = p.apply("elioore", &[&arg], &[]);
            let ord = p.apply("eliooord", &[&arg], &[]);
            let size = p.by(
                "absidd",
                &[
                    &arg_re,
                    &p.by(
                        "ltled",
                        &[&l(&zero_re), &arg_re, &p.by("simpld", &[&ord], &[])],
                        &[],
                    ),
                ],
                &[],
            );
            p.apply("sinq12gt0", &[&p.by("eqeltrd", &[&size, &arg], &[])], &[])
        };
        // Below it: the argument is in (−π, 0), and its negation in (0, π).
        let down = {
            let side = "( Im ` ( ( R - Q ) / ( P - Q ) ) ) < 0";
            let l = |s: &Said| p.lift(s, side);
            let neg = p.by("simpr", &[], &[("ph", &g), ("ps", side)]);
            let arg = p.apply("argimlt0", &[&p.joined(&[&l(&z), &neg])], &[]);
            let arg_re = p.apply("elioore", &[&arg], &[]);
            let ord = p.apply("eliooord", &[&arg], &[]);
            let size = p.by(
                "absnidd",
                &[
                    &arg_re,
                    &p.by(
                        "ltled",
                        &[&arg_re, &l(&zero_re), &p.by("simprd", &[&ord], &[])],
                        &[],
                    ),
                ],
                &[],
            );
            let neg_re = p.by("renegcld", &[&arg_re], &[]);
            let above = p.by(
                "mpbid",
                &[
                    &p.by("simprd", &[&ord], &[]),
                    &p.by("lt0neg1d", &[&arg_re], &[]),
                ],
                &[],
            );
            let below = p.by(
                "ltnegcon1d",
                &[&l(&pi_re), &arg_re, &p.by("simpld", &[&ord], &[])],
                &[],
            );
            let within = p.by(
                "mpbird",
                &[
                    &p.by("3jca", &[&neg_re, &above, &below], &[]),
                    &p.apply(
                        "elioo2",
                        &[&p.joined(&[
                            &l(&p.always(&p.by("0xr", &[], &[]), &g)),
                            &l(&pi_xr),
                        ])],
                        &[("C", &format!("-u {theta}"))],
                    ),
                ],
                &[],
            );
            p.apply(
                "sinq12gt0",
                &[&p.by("eqeltrd", &[&size, &within], &[])],
                &[],
            )
        };
        let said = p.by("mpjaodan", &[&down, &up, &sides], &[]);
        // The argument of z is the angle at Q.
        let value = p.by(
            "syl",
            &[
                &p.joined(&[&p.joined(&[&x, &xn]), &p.joined(&[&y, &yn])]),
                &p.by(
                    "angval",
                    &[&p.ang_defined()],
                    &[("A", "( P - Q )"), ("B", "( R - Q )")],
                ),
            ],
            &[],
        );
        let sine = p.by(
            "fveq2d",
            &[&p.by("fveq2d", &[&value], &[("F", "abs")])],
            &[("F", "sin")],
        );
        let said = p.by("breqtrrd", &[&said, &sine], &[]);
        let said = p.is(
            said,
            &format!("( {g} -> 0 < ( sin ` ( abs ` ( ( P - Q ) ang ( R - Q ) ) ) ) )"),
        );
        let said = p.curried(said, &conjuncts);
        let text = statement(&p, &said);
        (said, text)
    };
    finish(b, "gsinpos", said, text)
}

/// `glawsin`: the law of sines, `law-of-sines`.
///
/// Heron's formula (`heron`) gives the area from two sides and the sine of
/// the angle between them, and from the three sides alone. Taken at Q and at
/// R it is one area, since the three sides are the same three in another
/// order, so |PQ|·|QR|·|sin Q| = |QR|·|PR|·|sin R|. Half of |QR| is not 0
/// and cancels, and the size of the sine of an angle in (−π, π] is the sine
/// of its size (`gsinabs`).
fn law_of_sines(b: &mut Builder) -> Lemma {
    let tri = "( ( ( -. P = Q /\\ -. Q = R ) /\\ -. P = R ) /\\ -. ( ( R - P ) / ( Q - P ) ) e. RR )";
    let conjuncts = ["P e. CC", "Q e. CC", "R e. CC", tri];
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&conjuncts);
        let h = p.parts(&conjuncts);
        let (pc, qc, rc) = (&h[0], &h[1], &h[2]);
        let ap = p.apart(&h[3]);
        let rq = p.by("necomd", &[&ap.qr], &[]);
        let def = p.ang_defined();
        let eq = |t: &str| p.by("eqid", &[], &[("A", t)]);
        // Heron at the vertex `c`, with the angle from `bb` to `a`.
        let heron = |a: (&Said, &str),
                     bb: (&Said, &str),
                     c: (&Said, &str),
                     ac: &Said,
                     bc: &Said|
         -> Said {
            let (x, y, z) = (
                format!("( abs ` ( {} - {} ) )", bb.1, c.1),
                format!("( abs ` ( {} - {} ) )", a.1, c.1),
                format!("( abs ` ( {} - {} ) )", a.1, bb.1),
            );
            let o = format!("( ( {} - {} ) ang ( {} - {} ) )", bb.1, c.1, a.1, c.1);
            let s = format!("( ( ( {x} + {y} ) + {z} ) / 2 )");
            p.by(
                "heron",
                &[
                    &def,
                    &eq(&x),
                    &eq(&y),
                    &eq(&z),
                    &eq(&o),
                    &eq(&s),
                    a.0,
                    bb.0,
                    c.0,
                    ac,
                    bc,
                ],
                &[],
            )
        };
        let at_q = heron((rc, "R"), (pc, "P"), (qc, "Q"), &rq, &ap.pq);
        let at_r = heron((pc, "P"), (qc, "Q"), (rc, "R"), &ap.pr, &ap.qr);
        // The sides at R are the sides at Q: |QR| = |RQ|, |PR| = |RP|.
        let (pq_d, rq_d, rp_d) = (
            p.by("subcld", &[pc, qc], &[]),
            p.by("subcld", &[rc, qc], &[]),
            p.by("subcld", &[rc, pc], &[]),
        );
        let (a, b1, c1) = (
            p.by("abscld", &[&pq_d], &[]),
            p.by("abscld", &[&rq_d], &[]),
            p.by("abscld", &[&rp_d], &[]),
        );
        let (ac, b1c, c1c) = (
            p.by("recnd", &[&a], &[]),
            p.by("recnd", &[&b1], &[]),
            p.by("recnd", &[&c1], &[]),
        );
        let qr_is = p.by("abssubd", &[qc, rc], &[]);
        let pr_is = p.by("abssubd", &[pc, rc], &[]);
        let at_r_rhs = at_r.says.children()[1].children()[1].clone();
        let pieces = |said: &Said, v: &str| -> Said {
            p.cong(said, &p.term(v, "class"), &at_r_rhs)
                .expect("Heron's side")
        };
        let rhs1 = pieces(&qr_is, "( abs ` ( Q - R ) )");
        let mid = rhs1.says.children()[1].children()[1].clone();
        let rhs2 = p
            .cong(&pr_is, &p.term("( abs ` ( P - R ) )", "class"), &mid)
            .expect("Heron's side");
        let rhs = p.by("eqtrd", &[&rhs1, &rhs2], &[]);
        // Its half-perimeter is Q's: ( ( b + c ) + a ) = ( ( a + b ) + c ).
        let half = p.by(
            "eqtr4d",
            &[
                &p.by("addcomd", &[&p.by("addcld", &[&b1c, &c1c], &[]), &ac], &[]),
                &p.by("addassd", &[&ac, &b1c, &c1c], &[]),
            ],
            &[],
        );
        let s_at_r = "( ( ( ( abs ` ( R - Q ) ) + ( abs ` ( R - P ) ) ) + ( abs ` ( P - Q ) ) ) / 2 )";
        let s_at_q = "( ( ( ( abs ` ( P - Q ) ) + ( abs ` ( R - Q ) ) ) + ( abs ` ( R - P ) ) ) / 2 )";
        let half = p.by("oveq1d", &[&half], &[("C", "2"), ("F", "/")]);
        let half = p.is(half, &format!("( {g} -> {s_at_r} = {s_at_q} )"));
        let now = rhs.says.children()[1].children()[1].clone();
        let rhs3 = p
            .cong(&half, &p.term(s_at_r, "class"), &now)
            .expect("the half-perimeter");
        let rhs = p.by("eqtrd", &[&rhs, &rhs3], &[]);
        // ( S ( S − b ) ) ( ( S − c ) ( S − a ) ) is ( S ( S − a ) ) ( ( S − b ) ( S − c ) ).
        let s = p.by(
            "halfcld",
            &[&p.by("addcld", &[&p.by("addcld", &[&ac, &b1c], &[]), &c1c], &[])],
            &[],
        );
        let less = |x: &Said| p.by("subcld", &[&s, x], &[]);
        let (sa, sb, sc) = (less(&ac), less(&b1c), less(&c1c));
        let swap = p.by("mulcomd", &[&sc, &sa], &[]);
        let inner = p.by(
            "oveq2d",
            &[&swap],
            &[
                (
                    "C",
                    &format!("( {s_at_q} x. ( {s_at_q} - ( abs ` ( R - Q ) ) ) )"),
                ),
                ("F", "x."),
            ],
        );
        let product = p.by(
            "eqtrd",
            &[&inner, &p.by("mul4d", &[&s, &sb, &sa, &sc], &[])],
            &[],
        );
        let product = p.by("fveq2d", &[&product], &[("F", "sqrt")]);
        let rhs = p.by("eqtrd", &[&rhs, &product], &[]);
        // So the two areas are one: Heron at R equals Heron at Q.
        let areas = p.by("eqtr4d", &[&p.by("eqtrd", &[&at_r, &rhs], &[]), &at_q], &[]);
        // The size of the sine is the sine of the size, at Q and at R.
        // ( sin |O| = |sin O|, sin |O| as a number ), for the angle O from
        // x to y, which is in (−π, π] (`angcld`).
        let pi_re = p.always(&p.by("pire", &[], &[]), &g);
        let neg_pi = p.by("renegcld", &[&pi_re], &[]);
        let sine = |x: &Said,
                    xn: &Said,
                    y: &Said,
                    yn: &Said,
                    xt: &str,
                    yt: &str|
         -> (Said, Said) {
            let range = p.by("angcld", &[&def, x, xn, y, yn], &[]);
            let bounds = p.apply(
                "elioc2",
                &[&p.joined(&[&p.by("rexrd", &[&neg_pi], &[]), &pi_re])],
                &[("C", &format!("( {xt} ang {yt} )"))],
            );
            let parts = p.by("mpbid", &[&range, &bounds], &[]);
            let o_re = p.by("simp1d", &[&parts], &[]);
            let low = p.by(
                "ltled",
                &[&neg_pi, &o_re, &p.by("simp2d", &[&parts], &[])],
                &[],
            );
            let same = p.apply(
                "gsinabs",
                &[&p.joined(&[&o_re, &low, &p.by("simp3d", &[&parts], &[])])],
                &[],
            );
            let value = p.by(
                "recnd",
                &[&p.by(
                    "resincld",
                    &[&p.by("abscld", &[&p.by("recnd", &[&o_re], &[])], &[])],
                    &[],
                )],
                &[],
            );
            (same, value)
        };
        let pq_n = p.by("subne0d", &[pc, qc, &ap.pq], &[]);
        let rq_n = p.by("subne0d", &[rc, qc, &rq], &[]);
        let qr_d = p.by("subcld", &[qc, rc], &[]);
        let qr_n = p.by("subne0d", &[qc, rc, &ap.qr], &[]);
        let pr_d = p.by("subcld", &[pc, rc], &[]);
        let pr_n = p.by("subne0d", &[pc, rc, &ap.pr], &[]);
        let (sine_q, s_q) = sine(&pq_d, &pq_n, &rq_d, &rq_n, "( P - Q )", "( R - Q )");
        let (sine_r, s_r) = sine(&qr_d, &qr_n, &pr_d, &pr_n, "( Q - R )", "( P - R )");
        let (k_q, k_r) = (
            "( ( 1 / 2 ) x. ( ( abs ` ( P - Q ) ) x. ( abs ` ( R - Q ) ) ) )",
            "( ( 1 / 2 ) x. ( ( abs ` ( Q - R ) ) x. ( abs ` ( P - R ) ) ) )",
        );
        // k_R sin|O_R| = k_R |sin O_R| = k_Q |sin O_Q| = k_Q sin|O_Q|.
        let chain = p.by(
            "eqtr4d",
            &[
                &p.by(
                    "eqtrd",
                    &[
                        &p.by("oveq2d", &[&sine_r], &[("C", k_r), ("F", "x.")]),
                        &areas,
                    ],
                    &[],
                ),
                &p.by("oveq2d", &[&sine_q], &[("C", k_q), ("F", "x.")]),
            ],
            &[],
        );
        // Both sides are m = ½|RQ| times a side and a sine.
        let half = p.always(&p.by("halfcn", &[], &[]), &g);
        let c2 = p.by("recnd", &[&p.by("abscld", &[&pr_d], &[])], &[]);
        let m = p.by("mulcld", &[&half, &b1c], &[]);
        let m_text = "( ( 1 / 2 ) x. ( abs ` ( R - Q ) ) )";
        let left = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq2d",
                    &[&p.by("mulcomd", &[&ac, &b1c], &[])],
                    &[("C", "( 1 / 2 )"), ("F", "x.")],
                ),
                &p.by("eqcomd", &[&p.by("mulassd", &[&half, &b1c, &ac], &[])], &[]),
            ],
            &[],
        );
        let left = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq1d",
                    &[&left],
                    &[
                        ("C", "( sin ` ( abs ` ( ( P - Q ) ang ( R - Q ) ) ) )"),
                        ("F", "x."),
                    ],
                ),
                &p.by("mulassd", &[&m, &ac, &s_q], &[]),
            ],
            &[],
        );
        let right = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq2d",
                    &[&p.by(
                        "oveq1d",
                        &[&qr_is],
                        &[("C", "( abs ` ( P - R ) )"), ("F", "x.")],
                    )],
                    &[("C", "( 1 / 2 )"), ("F", "x.")],
                ),
                &p.by("eqcomd", &[&p.by("mulassd", &[&half, &b1c, &c2], &[])], &[]),
            ],
            &[],
        );
        let right = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq1d",
                    &[&right],
                    &[
                        ("C", "( sin ` ( abs ` ( ( Q - R ) ang ( P - R ) ) ) )"),
                        ("F", "x."),
                    ],
                ),
                &p.by("mulassd", &[&m, &c2, &s_r], &[]),
            ],
            &[],
        );
        let both = p.by(
            "eqtrd",
            &[&p.by("eqtr3d", &[&right, &chain], &[]), &left],
            &[],
        );
        let both = p.is(
            both,
            &format!(
                "( {g} -> ( {m_text} x. ( ( abs ` ( P - R ) ) x. ( sin ` ( abs ` ( ( Q - R ) ang ( P - R ) ) ) ) ) ) = ( {m_text} x. ( ( abs ` ( P - Q ) ) x. ( sin ` ( abs ` ( ( P - Q ) ang ( R - Q ) ) ) ) ) ) )"
            ),
        );
        let m_apart = p.by(
            "mulne0d",
            &[
                &half,
                &b1c,
                &p.by("gt0ne0d", &[&p.always(&p.by("halfgt0", &[], &[]), &g)], &[]),
                &p.by("absne0d", &[&rq_d, &rq_n], &[]),
            ],
            &[],
        );
        let said = p.by(
            "eqcomd",
            &[&p.by(
                "mulcanad",
                &[
                    &p.by("mulcld", &[&c2, &s_r], &[]),
                    &p.by("mulcld", &[&ac, &s_q], &[]),
                    &m,
                    &m_apart,
                    &both,
                ],
                &[],
            )],
            &[],
        );
        let said = p.is(
            said,
            &format!(
                "( {g} -> ( ( abs ` ( P - Q ) ) x. ( sin ` ( abs ` ( ( P - Q ) ang ( R - Q ) ) ) ) ) = ( ( abs ` ( P - R ) ) x. ( sin ` ( abs ` ( ( Q - R ) ang ( P - R ) ) ) ) ) )"
            ),
        );
        let said = p.curried(said, &conjuncts);
        let text = statement(&p, &said);
        (said, text)
    };
    finish(b, "glawsin", said, text)
}

/// `g90`: 90° is π/2, ( 90 · π ) / 180 = π / 2, since 180 is 90 · 2
/// (`dec0u`, `9t2e18`).
fn ninety(b: &mut Builder) -> Lemma {
    let (said, text) = {
        let p = Prover { b };
        let g = "T.";
        let closed = |s: Said| p.always(&s, g);
        let n0 = p.by("0nn0", &[], &[]);
        let n1 = p.by("1nn0", &[], &[]);
        let ten = p.by("nn0cnd", &[&closed(p.by("deccl", &[&n1, &n0], &[]))], &[]);
        let ninety_nn = closed(p.by("decnncl2", &[&p.by("9nn", &[], &[])], &[]));
        let ninety = p.by("nncnd", &[&ninety_nn], &[]);
        let nine = closed(p.by("9cn", &[], &[]));
        let two = closed(p.by("2cn", &[], &[]));
        let e1 = closed(p.by("dec0u", &[&p.by("9nn0", &[], &[])], &[]));
        let eighteen = p.by("deccl", &[&n1, &p.by("8nn0", &[], &[])], &[]);
        let e2 = closed(p.by("dec0u", &[&eighteen], &[]));
        let e3 = closed(p.by("9t2e18", &[], &[]));
        // 180 = 10 · 18 = 10 · ( 9 · 2 ) = ( 10 · 9 ) · 2 = 90 · 2.
        let split = p.by(
            "eqtrd",
            &[
                &p.by("eqcomd", &[&e2], &[]),
                &p.by(
                    "oveq2d",
                    &[&p.by("eqcomd", &[&e3], &[])],
                    &[("C", "; 1 0"), ("F", "x.")],
                ),
            ],
            &[],
        );
        let split = p.by(
            "eqtrd",
            &[
                &split,
                &p.by(
                    "eqtrd",
                    &[
                        &p.by(
                            "eqcomd",
                            &[&p.by("mulassd", &[&ten, &nine, &two], &[])],
                            &[],
                        ),
                        &p.by("oveq1d", &[&e1], &[("C", "2"), ("F", "x.")]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let said = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq2d",
                    &[&split],
                    &[("C", "( ; 9 0 x. _pi )"), ("F", "/")],
                ),
                &p.by(
                    "divcan5d",
                    &[
                        &closed(p.by("picn", &[], &[])),
                        &two,
                        &ninety,
                        &closed(p.by("2ne0", &[], &[])),
                        &p.by("nnne0d", &[&ninety_nn], &[]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let said = p.by("mptru", &[&said], &[]);
        let said = p.is(said, "( ( ; 9 0 x. _pi ) / ; ; 1 8 0 ) = ( _pi / 2 )");
        let text = statement(&p, &said);
        (said, text)
    };
    finish(b, "g90", said, text)
}

/// A point written as P + ξ·w, with w = Q − P: the coordinate it has along
/// PQ, and a proof that the point is that.
struct At {
    number: Said,
    is: Said,
    member: Said,
}

impl Prover<'_> {
    /// ( g -> ( ( c - b ) / ( a - b ) ) = ( ( γ - β ) / ( α - β ) ) ), for
    /// points a, b, c at coordinates α, β, γ along w from P, with α − β not
    /// 0. `along` is ( P ∈ ℂ, w ∈ ℂ, w ≠ 0 ).
    fn ratio(&self, a: &At, bb: &At, c: &At, along: [&Said; 3], apart: &Said) -> Said {
        let [pc, w, w_apart] = along;
        let diff = |x: &At, y: &At| -> Said {
            let raw = self.by("oveq12d", &[&x.is, &y.is], &[("F", "-")]);
            let xw = self.by("mulcld", &[&x.number, w], &[]);
            let yw = self.by("mulcld", &[&y.number, w], &[]);
            let gathered = self.by(
                "eqtrd",
                &[
                    &self.by("pnpcand", &[pc, &xw, &yw], &[]),
                    &self.by(
                        "eqcomd",
                        &[&self.by("subdird", &[&x.number, &y.number, w], &[])],
                        &[],
                    ),
                ],
                &[],
            );
            self.by("eqtrd", &[&raw, &gathered], &[])
        };
        let top = diff(c, bb);
        let low = diff(a, bb);
        let both = self.by("oveq12d", &[&top, &low], &[("F", "/")]);
        let cb = self.by("subcld", &[&c.number, &bb.number], &[]);
        let ab = self.by("subcld", &[&a.number, &bb.number], &[]);
        self.by(
            "eqtrd",
            &[
                &both,
                &self.by("divcan5rd", &[&cb, &ab, w, apart, w_apart], &[]),
            ],
            &[],
        )
    }

    /// ( g -> x =/= y ), for points at coordinates ξ and η along w with
    /// ξ − η not 0: x − y is ( ξ − η ) w.
    fn points_apart(&self, x: &At, y: &At, along: [&Said; 3], apart: &Said) -> Said {
        let [pc, w, w_apart] = along;
        let raw = self.by("oveq12d", &[&x.is, &y.is], &[("F", "-")]);
        let xw = self.by("mulcld", &[&x.number, w], &[]);
        let yw = self.by("mulcld", &[&y.number, w], &[]);
        let gathered = self.by(
            "eqtrd",
            &[
                &raw,
                &self.by(
                    "eqtrd",
                    &[
                        &self.by("pnpcand", &[pc, &xw, &yw], &[]),
                        &self.by(
                            "eqcomd",
                            &[&self.by("subdird", &[&x.number, &y.number, w], &[])],
                            &[],
                        ),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let product = self.by(
            "mulne0d",
            &[
                &self.by("subcld", &[&x.number, &y.number], &[]),
                w,
                apart,
                w_apart,
            ],
            &[],
        );
        self.by(
            "subne0ad",
            &[
                &x.member,
                &y.member,
                &self.by("eqnetrd", &[&gathered, &product], &[]),
            ],
            &[],
        )
    }
}

/// What `altitude-foot` says of x, as set.mm writes it.
fn foot(x: &str) -> String {
    let ninety = "( ( ; 9 0 x. _pi ) / ; ; 1 8 0 )";
    format!(
        "( ( ( ( ( P =/= {x} /\\ ( ( Q - {x} ) / ( P - {x} ) ) e. RR /\\ ( ( Q - {x} ) / ( P - {x} ) ) < 0 ) \
         /\\ ( abs ` ( ( P - {x} ) ang ( R - {x} ) ) ) = {ninety} ) \
         /\\ ( abs ` ( ( Q - {x} ) ang ( R - {x} ) ) ) = {ninety} ) \
         /\\ ( ( ( -. P = {x} /\\ -. {x} = R ) /\\ -. P = R ) /\\ -. ( ( R - P ) / ( {x} - P ) ) e. RR ) ) \
         /\\ ( ( ( -. Q = {x} /\\ -. {x} = R ) /\\ -. Q = R ) /\\ -. ( ( R - Q ) / ( {x} - Q ) ) e. RR ) )"
    )
}

impl Prover<'_> {
    /// ( g -> -. q e. RR ), from q a number whose imaginary part is not 0.
    fn not_real(&self, q: &Said, im_apart: &Said) -> Said {
        self.by(
            "mtbird",
            &[
                &self.by("neneqd", &[im_apart], &[]),
                &self.apply("reim0b", &[q], &[]),
            ],
            &[],
        )
    }

    /// ( g -> ( abs ` ( X ang Y ) ) = 90° ), from Re ( Y / X ) = 0: the
    /// angle is ±π/2 (`angrteqvd`), whose size is π/2 either way (`g90`).
    #[allow(clippy::too_many_arguments)]
    fn right_angle(
        &self,
        g: &str,
        x: &Said,
        xn: &Said,
        y: &Said,
        yn: &Said,
        re_zero: &Said,
    ) -> Said {
        let def = self.ang_defined();
        let pair = self.by(
            "mpbird",
            &[re_zero, &self.by("angrteqvd", &[&def, x, xn, y, yn], &[])],
            &[],
        );
        let either = self.apply("elpri", &[&pair], &[]);
        let half = self.by(
            "rphalfcld",
            &[&self.always(&self.by("pirp", &[], &[]), g)],
            &[],
        );
        let half_re = self.by("rpred", &[&half], &[]);
        let half_ge = self.by("rpge0d", &[&half], &[]);
        let theta = self.show(&pair.says.children()[1].children()[0]);
        let case = |side: &str, negated: bool| -> Said {
            let l = |s: &Said| self.lift(s, side);
            let is = self.by("simpr", &[], &[("ph", g), ("ps", side)]);
            let size = self.by("fveq2d", &[&is], &[("F", "abs")]);
            let size = if negated {
                self.by(
                    "eqtrd",
                    &[
                        &size,
                        &self.by(
                            "absnegd",
                            &[&self.by("recnd", &[&l(&half_re)], &[])],
                            &[],
                        ),
                    ],
                    &[],
                )
            } else {
                size
            };
            let said = self.by(
                "eqtrd",
                &[
                    &size,
                    &self.by("absidd", &[&l(&half_re), &l(&half_ge)], &[]),
                ],
                &[],
            );
            self.by("ex", &[&said], &[])
        };
        let up = case(&format!("{theta} = ( _pi / 2 )"), false);
        let down = case(&format!("{theta} = -u ( _pi / 2 )"), true);
        let size = self.by("mpjaod", &[&up, &down, &either], &[]);
        self.by(
            "eqtr4d",
            &[&size, &self.always(&self.by("g90", &[], &[]), g)],
            &[],
        )
    }
}

/// `galtfoot`: the foot of the altitude from a right angle,
/// `altitude-foot`.
///
/// Put each point at a coordinate along w = Q − P from P: P at 0, Q at 1, R
/// at z = (R − P)/w, which is not real, and D at t = Re z. Every quotient
/// the item names is then (γ − β)/(α − β) of three coordinates (`ratio`).
/// The right angle at R says Re((1 − z)/(0 − z)) = 0, so Re(1/z) = 1 and
/// t = |z|² = t² + s² with s = Im z: t is positive and t(1 − t) = s² is
/// too, so D is strictly between P and Q. R − D is i·s·w, a right angle to
/// both P − D and Q − D.
fn altitude(b: &mut Builder) -> Lemma {
    let tri = "( ( ( -. P = Q /\\ -. Q = R ) /\\ -. P = R ) /\\ -. ( ( R - P ) / ( Q - P ) ) e. RR )";
    let right =
        "( abs ` ( ( P - R ) ang ( Q - R ) ) ) = ( ( ; 9 0 x. _pi ) / ; ; 1 8 0 )";
    let conjuncts = ["P e. CC", "Q e. CC", "R e. CC", tri, right];
    let z = "( ( R - P ) / ( Q - P ) )";
    let t = format!("( Re ` {z} )");
    let d = format!("( P + ( {t} x. ( Q - P ) ) )");
    let (said, text) = {
        let p = Prover { b };
        let g = Prover::conjoined(&conjuncts);
        let h = p.parts(&conjuncts);
        let (pc, qc, rc) = (&h[0], &h[1], &h[2]);
        let ap = p.apart(&h[3]);
        let not_line = p.by("simprd", &[&h[3]], &[]);
        let three = p.by("simpld", &[&h[3]], &[]);
        let not_pr = p.by("simprd", &[&three], &[]);
        let not_qr = p.by("simprd", &[&p.by("simpld", &[&three], &[])], &[]);
        let w = p.by("subcld", &[qc, pc], &[]);
        let wn = p.by("subne0d", &[qc, pc, &p.by("necomd", &[&ap.pq], &[])], &[]);
        let along = [pc, &w, &wn];
        let rp = p.by("subcld", &[rc, pc], &[]);
        let zc = p.by("divcld", &[&rp, &w, &wn], &[]);
        let s_apart =
            p.off_line(&zc, &p.by("eqidd", &[], &[("ph", &g), ("A", z)]), &not_line);
        let s_re = p.by("imcld", &[&zc], &[]);
        let s_c = p.by("recnd", &[&s_re], &[]);
        let t_re = p.by("recld", &[&zc], &[]);
        let t_c = p.by("recnd", &[&t_re], &[]);
        let z_apart = p.nonzero(z, &g, &s_apart);
        let zero = p.by("0cnd", &[], &[("ph", &g)]);
        let one = p.by("1cnd", &[], &[("ph", &g)]);
        let zero_re = p.always(&p.by("0re", &[], &[]), &g);
        let one_re = p.always(&p.by("1re", &[], &[]), &g);
        // The four points along w.
        let at_p = At {
            number: zero.clone(),
            is: p.by(
                "eqcomd",
                &[&p.by(
                    "eqtrd",
                    &[
                        &p.by(
                            "oveq2d",
                            &[&p.by("mul02d", &[&w], &[])],
                            &[("C", "P"), ("F", "+")],
                        ),
                        &p.by("addridd", &[pc], &[]),
                    ],
                    &[],
                )],
                &[],
            ),
            member: pc.clone(),
        };
        let at_q = At {
            number: one.clone(),
            is: p.by(
                "eqcomd",
                &[&p.by(
                    "eqtrd",
                    &[
                        &p.by(
                            "oveq2d",
                            &[&p.by("mullidd", &[&w], &[])],
                            &[("C", "P"), ("F", "+")],
                        ),
                        &p.by("pncan3d", &[pc, qc], &[]),
                    ],
                    &[],
                )],
                &[],
            ),
            member: qc.clone(),
        };
        let at_r = At {
            number: zc.clone(),
            is: p.by(
                "eqcomd",
                &[&p.by(
                    "eqtrd",
                    &[
                        &p.by(
                            "oveq2d",
                            &[&p.by("divcan1d", &[&rp, &w, &wn], &[])],
                            &[("C", "P"), ("F", "+")],
                        ),
                        &p.by("pncan3d", &[pc, rc], &[]),
                    ],
                    &[],
                )],
                &[],
            ),
            member: rc.clone(),
        };
        let dc = p.by("addcld", &[pc, &p.by("mulcld", &[&t_c, &w], &[])], &[]);
        let at_d = At {
            number: t_c.clone(),
            is: p.by("eqidd", &[], &[("ph", &g), ("A", &d)]),
            member: dc.clone(),
        };

        // The right angle at R: Re((Q − R)/(P − R)) = 0, and that quotient is
        // ( 1 − z ) / ( 0 − z ) = 1 − 1/z.
        let def = p.ang_defined();
        let pr = p.by("subcld", &[pc, rc], &[]);
        let pr_n = p.by("subne0d", &[pc, rc, &ap.pr], &[]);
        let qr = p.by("subcld", &[qc, rc], &[]);
        let qr_n = p.by("subne0d", &[qc, rc, &ap.qr], &[]);
        let theta_r = "( ( P - R ) ang ( Q - R ) )";
        let range = p.by("angcld", &[&def, &pr, &pr_n, &qr, &qr_n], &[]);
        let pi_re = p.always(&p.by("pire", &[], &[]), &g);
        let neg_pi = p.by("renegcld", &[&pi_re], &[]);
        let bounds = p.apply(
            "elioc2",
            &[&p.joined(&[&p.by("rexrd", &[&neg_pi], &[]), &pi_re])],
            &[("C", theta_r)],
        );
        let theta_re = p.by("simp1d", &[&p.by("mpbid", &[&range, &bounds], &[])], &[]);
        let size = p.by(
            "eqtrd",
            &[&h[4], &p.always(&p.by("g90", &[], &[]), &g)],
            &[],
        );
        let half_text = "( _pi / 2 )";
        let to_pair = |side: &str, negated: bool| -> Said {
            let l = |s: &Said| p.lift(s, side);
            let is = p.by("simpr", &[], &[("ph", &g), ("ps", side)]);
            let said = p.by("eqtr3d", &[&is, &l(&size)], &[]);
            let said = if negated {
                p.by(
                    "eqcomd",
                    &[&p.by(
                        "mpbid",
                        &[
                            &said,
                            &p.by(
                                "negcon1d",
                                &[
                                    &p.by("recnd", &[&l(&theta_re)], &[]),
                                    &p.by(
                                        "recnd",
                                        &[&l(&p.by("rehalfcld", &[&pi_re], &[]))],
                                        &[],
                                    ),
                                ],
                                &[],
                            ),
                        ],
                        &[],
                    )],
                    &[],
                )
            } else {
                said
            };
            let said = if negated {
                p.by(
                    "olcd",
                    &[&said],
                    &[("ch", &format!("{theta_r} = {half_text}"))],
                )
            } else {
                p.by(
                    "orcd",
                    &[&said],
                    &[("ch", &format!("{theta_r} = -u {half_text}"))],
                )
            };
            p.by("ex", &[&said], &[])
        };
        let either = p.by(
            "mpjaod",
            &[
                &to_pair(&format!("( abs ` {theta_r} ) = {theta_r}"), false),
                &to_pair(&format!("( abs ` {theta_r} ) = -u {theta_r}"), true),
                &p.apply("absor", &[&theta_re], &[]),
            ],
            &[],
        );
        let pair = p.by(
            "mpbird",
            &[
                &either,
                &p.apply(
                    "elprg",
                    &[&p.by("recnd", &[&theta_re], &[])],
                    &[("V", "CC"), ("B", half_text), ("C", "-u ( _pi / 2 )")],
                ),
            ],
            &[],
        );
        let re_zero = p.by(
            "mpbid",
            &[
                &pair,
                &p.by("angrteqvd", &[&def, &pr, &pr_n, &qr, &qr_n], &[]),
            ],
            &[],
        );
        let z_neg = p.by(
            "subne0d",
            &[&zero, &zc, &p.by("necomd", &[&z_apart], &[])],
            &[],
        );
        let quot = p.ratio(&at_p, &at_r, &at_q, along, &z_neg);
        let re_zero = p.by(
            "eqtr3d",
            &[&p.by("fveq2d", &[&quot], &[("F", "Re")]), &re_zero],
            &[],
        );
        // ( 1 − z ) / ( 0 − z ) = ( −( z − 1 ) ) / ( −z ) = ( z − 1 ) / z
        // = 1 − 1/z.
        let zm1 = p.by("subcld", &[&zc, &one], &[]);
        let flipped = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq12d",
                    &[
                        &p.by("eqcomd", &[&p.by("negsubdi2d", &[&zc, &one], &[])], &[]),
                        &p.by(
                            "eqcomd",
                            &[&p.always(&p.by("df-neg", &[], &[("A", z)]), &g)],
                            &[],
                        ),
                    ],
                    &[("F", "/")],
                ),
                &p.by("div2negd", &[&zm1, &zc, &z_apart], &[]),
            ],
            &[],
        );
        let rz = p.by("reccld", &[&zc, &z_apart], &[]);
        let flipped = p.by(
            "eqtrd",
            &[
                &flipped,
                &p.by(
                    "eqtrd",
                    &[
                        &p.by("divsubdird", &[&zc, &one, &zc, &z_apart], &[]),
                        &p.by(
                            "oveq1d",
                            &[&p.by("dividd", &[&zc, &z_apart], &[])],
                            &[("C", &format!("( 1 / {z} )")), ("F", "-")],
                        ),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let re_zero = p.by(
            "eqtr3d",
            &[&p.by("fveq2d", &[&flipped], &[("F", "Re")]), &re_zero],
            &[],
        );
        let re_zero = p.by(
            "eqtr3d",
            &[
                &p.by(
                    "eqtrd",
                    &[
                        &p.by("resubd", &[&one, &rz], &[]),
                        &p.by(
                            "oveq1d",
                            &[&p.always(&p.by("re1", &[], &[]), &g)],
                            &[("C", &format!("( Re ` ( 1 / {z} ) )")), ("F", "-")],
                        ),
                    ],
                    &[],
                ),
                &re_zero,
            ],
            &[],
        );
        let re_rec = p.by(
            "subeq0d",
            &[
                &one,
                &p.by("recnd", &[&p.by("recld", &[&rz], &[])], &[]),
                &re_zero,
            ],
            &[],
        );
        // Re ( 1 / z ) = t / |z|², so t = |z|².
        let size = p.by(
            "rpexpcld",
            &[
                &p.by("absrpcld", &[&zc, &z_apart], &[]),
                &p.always(&p.by("2z", &[], &[]), &g),
            ],
            &[],
        );
        let k_re = p.by("rpred", &[&size], &[]);
        let k_c = p.by("recnd", &[&k_re], &[]);
        let k_n = p.by("rpne0d", &[&size], &[]);
        let rec = p.apply("recval", &[&p.joined(&[&zc, &z_apart])], &[]);
        let re_rec_is = p.by(
            "eqtrd",
            &[
                &p.by("fveq2d", &[&rec], &[("F", "Re")]),
                &p.by("redivd", &[&k_re, &p.by("cjcld", &[&zc], &[]), &k_n], &[]),
            ],
            &[],
        );
        let re_rec_is = p.by(
            "eqtrd",
            &[
                &re_rec_is,
                &p.by(
                    "oveq1d",
                    &[&p.by("recjd", &[&zc], &[])],
                    &[("C", &format!("( ( abs ` {z} ) ^ 2 )")), ("F", "/")],
                ),
            ],
            &[],
        );
        let unit = p.by("eqtrd", &[&re_rec, &re_rec_is], &[]);
        let t_is = p.by(
            "eqtrd",
            &[
                &p.by(
                    "eqcomd",
                    &[&p.by("divcan1d", &[&t_c, &k_c, &k_n], &[])],
                    &[],
                ),
                &p.by(
                    "eqtrd",
                    &[
                        &p.by(
                            "oveq1d",
                            &[&p.by("eqcomd", &[&unit], &[])],
                            &[("C", &format!("( ( abs ` {z} ) ^ 2 )")), ("F", "x.")],
                        ),
                        &p.by("mullidd", &[&k_c], &[]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        let t_pos = p.by("breqtrrd", &[&p.by("rpgt0d", &[&size], &[]), &t_is], &[]);
        // t = t² + s², so t ( 1 − t ) = s², which is positive.
        let t_sq = p.by("eqtrd", &[&t_is, &p.apply("absvalsq2", &[&zc], &[])], &[]);
        let t2 = p.by("sqcld", &[&t_c], &[]);
        let s2 = p.by("sqcld", &[&s_c], &[]);
        let rest = p.by(
            "mpbird",
            &[
                &p.by("eqcomd", &[&t_sq], &[]),
                &p.by("subaddd", &[&t_c, &t2, &s2], &[]),
            ],
            &[],
        );
        let product = p.by(
            "eqtrd",
            &[
                &p.by("subdid", &[&t_c, &one, &t_c], &[]),
                &p.by(
                    "oveq12d",
                    &[
                        &p.by("mulridd", &[&t_c], &[]),
                        &p.by("eqcomd", &[&p.by("sqvald", &[&t_c], &[])], &[]),
                    ],
                    &[("F", "-")],
                ),
            ],
            &[],
        );
        let product = p.by("eqtrd", &[&product, &rest], &[]);
        let product_pos = p.by(
            "breqtrrd",
            &[&p.by("sqgt0d", &[&s_re, &s_apart], &[]), &product],
            &[],
        );
        let omt_re = p.by("resubcld", &[&one_re, &t_re], &[]);
        let omt_pos = p.apply(
            "prodgt0",
            &[&p.joined(&[
                &p.joined(&[&t_re, &omt_re]),
                &p.joined(&[
                    &p.by("ltled", &[&zero_re, &t_re, &t_pos], &[]),
                    &product_pos,
                ]),
            ])],
            &[],
        );
        let t_apart = p.by("gt0ne0d", &[&t_pos], &[]);
        let t_below = p.by(
            "mpbird",
            &[&omt_pos, &p.by("posdifd", &[&t_re, &one_re], &[])],
            &[],
        );
        let t_not_one = p.by("ltned", &[&t_re, &t_below], &[]);
        let zero_t = p.by(
            "subne0d",
            &[&zero, &t_c, &p.by("necomd", &[&t_apart], &[])],
            &[],
        );
        let one_t = p.by(
            "subne0d",
            &[&one, &t_c, &p.by("necomd", &[&t_not_one], &[])],
            &[],
        );
        let t_zero = p.by("subne0d", &[&t_c, &zero, &t_apart], &[]);
        let t_one = p.by("subne0d", &[&t_c, &one, &t_not_one], &[]);
        // z − t is i s, not 0.
        let i_c = p.always(&p.by("ax-icn", &[], &[]), &g);
        let is_c = p.by("mulcld", &[&i_c, &s_c], &[]);
        let z_t = p.by(
            "eqtrd",
            &[
                &p.by(
                    "oveq1d",
                    &[&p.apply("replim", &[&zc], &[])],
                    &[("C", &t), ("F", "-")],
                ),
                &p.by("pncan2d", &[&t_c, &is_c], &[]),
            ],
            &[],
        );
        let z_t_apart = p.by(
            "eqnetrd",
            &[
                &z_t,
                &p.by(
                    "mulne0d",
                    &[&i_c, &s_c, &p.always(&p.by("ine0", &[], &[]), &g), &s_apart],
                    &[],
                ),
            ],
            &[],
        );
        let re_z_t = p.by(
            "eqtrd",
            &[
                &p.by("resubd", &[&zc, &t_c], &[]),
                &p.by(
                    "eqtrd",
                    &[
                        &p.by(
                            "oveq2d",
                            &[&p.by("rered", &[&t_re], &[])],
                            &[("C", &t), ("F", "-")],
                        ),
                        &p.by("subidd", &[&t_c], &[]),
                    ],
                    &[],
                ),
            ],
            &[],
        );
        // D between P and Q: ( Q − D ) / ( P − D ) = ( 1 − t ) / ( 0 − t ),
        // −( ( 1 − t ) / t ), negative.
        let p_d = p.points_apart(&at_p, &at_d, along, &zero_t);
        let qd = p.ratio(&at_p, &at_d, &at_q, along, &zero_t);
        let value = p.by(
            "eqtr4d",
            &[
                &p.by(
                    "oveq2d",
                    &[&p.by(
                        "eqcomd",
                        &[&p.always(&p.by("df-neg", &[], &[("A", &t)]), &g)],
                        &[],
                    )],
                    &[("C", &format!("( 1 - {t} )")), ("F", "/")],
                ),
                &p.by(
                    "divneg2d",
                    &[&p.by("subcld", &[&one, &t_c], &[]), &t_c, &t_apart],
                    &[],
                ),
            ],
            &[],
        );
        let ratio_pos = p.by("divgt0d", &[&omt_re, &t_re, &omt_pos, &t_pos], &[]);
        let ratio_re = p.by("redivcld", &[&omt_re, &t_re, &t_apart], &[]);
        let below = p.by(
            "mpbid",
            &[&ratio_pos, &p.by("lt0neg2d", &[&ratio_re], &[])],
            &[],
        );
        let qd_value = p.by("eqtrd", &[&qd, &value], &[]);
        let between_d = p.by(
            "3jca",
            &[
                &p_d,
                &p.by(
                    "eqeltrd",
                    &[&qd_value, &p.by("renegcld", &[&ratio_re], &[])],
                    &[],
                ),
                &p.by("eqbrtrd", &[&qd_value, &below], &[]),
            ],
            &[],
        );
        // Right angles at D: ( R − D ) over ( P − D ) or ( Q − D ) has real
        // part Re ( z − t ) over a real number, which is 0.
        let r_d = p.points_apart(&at_r, &at_d, along, &z_t_apart);
        let q_d = p.points_apart(&at_q, &at_d, along, &one_t);
        let rd = p.by("subcld", &[rc, &dc], &[]);
        let rd_n = p.by("subne0d", &[rc, &dc, &r_d], &[]);
        let zt_c = p.by("subcld", &[&zc, &t_c], &[]);
        let flat = |x: &At, low: &Said, low_re: &Said| -> Said {
            let q = p.ratio(x, &at_d, &at_r, along, low);
            let re = p.by(
                "eqtrd",
                &[
                    &p.by("fveq2d", &[&q], &[("F", "Re")]),
                    &p.by("redivd", &[low_re, &zt_c, low], &[]),
                ],
                &[],
            );
            let lowc = p.by("recnd", &[low_re], &[]);
            p.by(
                "eqtrd",
                &[
                    &re,
                    &p.by(
                        "eqtrd",
                        &[
                            &p.by(
                                "oveq1d",
                                &[&re_z_t],
                                &[
                                    (
                                        "C",
                                        &p.show(&lowc.says.children()[1].children()[0]),
                                    ),
                                    ("F", "/"),
                                ],
                            ),
                            &p.by("div0d", &[&lowc, low], &[]),
                        ],
                        &[],
                    ),
                ],
                &[],
            )
        };
        let zero_t_re = p.by("resubcld", &[&zero_re, &t_re], &[]);
        let one_t_re = p.by("resubcld", &[&one_re, &t_re], &[]);
        let pdx = p.by("subcld", &[pc, &dc], &[]);
        let pdx_n = p.by("subne0d", &[pc, &dc, &p_d], &[]);
        let qdx = p.by("subcld", &[qc, &dc], &[]);
        let qdx_n = p.by("subne0d", &[qc, &dc, &q_d], &[]);
        let right_p = p.right_angle(
            &g,
            &pdx,
            &pdx_n,
            &rd,
            &rd_n,
            &flat(&at_p, &zero_t, &zero_t_re),
        );
        let right_q = p.right_angle(
            &g,
            &qdx,
            &qdx_n,
            &rd,
            &rd_n,
            &flat(&at_q, &one_t, &one_t_re),
        );
        // P, D, R and Q, D, R are triangles: ( z − 0 ) / ( t − 0 ) and
        // ( z − 1 ) / ( t − 1 ) have imaginary part s over a real number.
        let off = |x: &At,
                   low: &Said,
                   low_re: &Said,
                   xi_c: &Said,
                   im_xi: &Said|
         -> Said {
            let q = p.ratio(&at_d, x, &at_r, along, low);
            let zx = p.by("subcld", &[&zc, xi_c], &[]);
            let im = p.by(
                "eqtrd",
                &[
                    &p.by("imdivd", &[low_re, &zx, low], &[]),
                    &p.by(
                        "oveq1d",
                        &[&p.by(
                            "eqtrd",
                            &[
                                &p.by("imsubd", &[&zc, xi_c], &[]),
                                &p.by(
                                    "eqtrd",
                                    &[
                                        &p.by(
                                            "oveq2d",
                                            &[im_xi],
                                            &[
                                                ("C", &format!("( Im ` {z} )")),
                                                ("F", "-"),
                                            ],
                                        ),
                                        &p.by("subid1d", &[&s_c], &[]),
                                    ],
                                    &[],
                                ),
                            ],
                            &[],
                        )],
                        &[
                            ("C", &p.show(&low_re.says.children()[1].children()[0])),
                            ("F", "/"),
                        ],
                    ),
                ],
                &[],
            );
            let lowc = p.by("recnd", &[low_re], &[]);
            let im_apart = p.by(
                "eqnetrd",
                &[&im, &p.by("divne0d", &[&s_c, &lowc, &s_apart, low], &[])],
                &[],
            );
            let not_q = p.not_real(&p.by("divcld", &[&zx, &lowc, low], &[]), &im_apart);
            p.by(
                "mtbird",
                &[&not_q, &p.by("eleq1d", &[&q], &[("C", "RR")])],
                &[],
            )
        };
        let im0 = p.always(&p.by("im0", &[], &[]), &g);
        let im1 = p.always(&p.by("im1", &[], &[]), &g);
        let t_zero_re = p.by("resubcld", &[&t_re, &zero_re], &[]);
        let t_one_re = p.by("resubcld", &[&t_re, &one_re], &[]);
        let d_r = p.by("neneqd", &[&p.by("necomd", &[&r_d], &[])], &[]);
        let tri_p = p.by(
            "jca31",
            &[&p.by("neneqd", &[&p_d], &[]), &d_r, &not_pr],
            &[],
        );
        let tri_p = p.by(
            "jca",
            &[&tri_p, &off(&at_p, &t_zero, &t_zero_re, &zero, &im0)],
            &[],
        );
        let tri_q = p.by(
            "jca31",
            &[&p.by("neneqd", &[&q_d], &[]), &d_r, &not_qr],
            &[],
        );
        let tri_q = p.by(
            "jca",
            &[&tri_q, &off(&at_q, &t_one, &t_one_re, &one, &im1)],
            &[],
        );
        let body = p.joined(&[&between_d, &right_p, &right_q, &tri_p, &tri_q]);
        let body = p.is(body, &format!("( {g} -> {} )", foot(&d)));
        // There is such a point: D.
        let x_is = format!("x = {d}");
        let x_eq = p.by("simpr", &[], &[("ph", &g), ("ps", &x_is)]);
        let swap = p
            .cong(&x_eq, &p.term("x", "class"), &p.term(&foot("x"), "wff"))
            .expect("the claim names x");
        let said = p.by("rspcedvd", &[&dc, &swap, &body], &[]);
        let said = p.curried(said, &conjuncts);
        let text = statement(&p, &said);
        (said, text)
    };
    finish(b, "galtfoot", said, text)
}

/// Each triangles lemma, in the order a later one may take an earlier.
pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![
        distance_real(b),
        between_turned(b),
        along_segment(b),
        segment_sum(b),
        sine_of_size(b),
        sine_positive(b),
        law_of_sines(b),
        ninety(b),
        altitude(b),
    ]
}

//! thm:proofs/sqrt2-irrational/sqrt2-irrational as a Metamath proof.
//!
//! The proof cites thm:proofs/sqrt2-irrational/even-square, which
//! `parity.mm` proves, so this file builds on that one rather than on set.mm
//! directly. thm:proofs/sqrt2-irrational/lowest-terms and the three `algebra`
//! steps are axioms here; everything else is the real thing.

use crate::mm::spell::{
    cel, div, dvds, eq, exp, le, lt, mul, ne, rex, w3a, wa, wb, wi, wn,
};
use crate::seq;

const TWO: &str = "c2";
const ONE: &str = "c1";
const ZERO: &str = "cc0";
const FOUR: &str = "c4";
const PV: &str = "vp cv";
const QV: &str = "vq cv";
const RV: &str = "vr cv";
const SV: &str = "vs cv";
const DV: &str = "vd cv";
const NV: &str = "vn cv";
const SQ2: &str = "c2 csqrt cfv";
const AV: &str = "cA";
const BV: &str = "cB";

/// th -> claim, from a closed proof of claim.
fn a1i(claim: &str, th: &str, pf: &str) -> String {
    seq!(claim, th, pf, "a1i")
}

fn zcn(th: &str, x: &str, pf: &str) -> String {
    seq!(th, cel(x, "cz"), cel(x, "cc"), pf, x, "zcn", "syl")
}

fn zre(th: &str, x: &str, pf: &str) -> String {
    seq!(th, cel(x, "cz"), cel(x, "cr"), pf, x, "zre", "syl")
}

fn zsq(th: &str, x: &str, pf: &str) -> String {
    seq!(
        th,
        cel(x, "cz"),
        cel(exp(x, TWO), "cz"),
        pf,
        x,
        "zsqcl",
        "syl"
    )
}

/// ( th /\ added ) -> claim, from th -> claim.
fn adr(th: &str, claim: &str, added: &str, pf: &str) -> String {
    seq!(th, claim, added, pf, "adantr")
}

/// Carry a fact proved at `outer` into the scope that `adds` opens.
fn lift(claim: &str, pf: &str, outer: &str, adds: &[&str]) -> String {
    let mut pf = pf.to_string();
    let mut outer = outer.to_string();
    for add in adds {
        pf = adr(&outer, claim, add, &pf);
        outer = wa(&outer, add);
    }
    pf
}

/// th -> ( 2 x. ( 2 x. X ) ) = ( 4 x. X ), the one numeral fact needed.
fn two_of(th: &str, x: &str, p_x: &str) -> String {
    let assoc = seq!(
        th,
        mul(mul(TWO, TWO), x),
        mul(TWO, mul(TWO, x)),
        seq!(
            th,
            w3a(cel(TWO, "cc"), cel(TWO, "cc"), cel(x, "cc")),
            eq(mul(mul(TWO, TWO), x), mul(TWO, mul(TWO, x))),
            seq!(
                th,
                cel(TWO, "cc"),
                cel(TWO, "cc"),
                cel(x, "cc"),
                seq!(th, "2cnd"),
                seq!(th, "2cnd"),
                p_x,
                "3jca"
            ),
            TWO,
            TWO,
            x,
            "mulass",
            "syl"
        ),
        "eqcomd"
    );
    seq!(
        th,
        mul(TWO, mul(TWO, x)),
        mul(mul(TWO, TWO), x),
        mul(FOUR, x),
        assoc,
        seq!(
            th,
            mul(TWO, TWO),
            FOUR,
            x,
            "cmul",
            a1i(&eq(mul(TWO, TWO), FOUR), th, "2t2e4"),
            "oveq1d"
        ),
        "eqtrd"
    )
}

/// th -> 2 || X, where p_eq proves th -> X = ( 2 x. Y ).
///
/// This is `def:stdlib/divisibility/even` used to conclude, as step 6 of
/// odd-square was. The kernel writes the witness equation as
/// ( k x. 2 ) = X where the corpus writes X = 2k, so the two ends of it have
/// to be turned round.
fn even_of(th: &str, x: &str, y: &str, p_eq: &str, p_yzz: &str, p_xzz: &str) -> String {
    let comm = seq!(
        th,
        TWO,
        y,
        a1i(&cel(TWO, "cc"), th, "2cn"),
        zcn(th, y, p_yzz),
        "mulcomd"
    );
    let flip = seq!(
        th,
        x,
        mul(y, TWO),
        seq!(th, x, mul(TWO, y), mul(y, TWO), p_eq, comm, "eqtrd"),
        "eqcomd"
    );
    let ph = eq(mul(NV, TWO), x);
    let ps = eq(mul(y, TWO), x);
    let hyp = seq!(
        eq(NV, y),
        mul(NV, TWO),
        mul(y, TWO),
        x,
        seq!(NV, y, TWO, "cmul", "oveq1"),
        "eqeq1d"
    );
    let ex = rex(&ph, "vn", "cz");
    let wit = seq!(
        th,
        wa(cel(y, "cz"), &ps),
        ex,
        seq!(th, cel(y, "cz"), ps, p_yzz, flip, "jca"),
        ph,
        ps,
        "vn",
        y,
        "cz",
        hyp,
        "rspcev",
        "syl"
    );
    let bic = seq!(
        th,
        wa(cel(TWO, "cz"), cel(x, "cz")),
        wb(dvds(TWO, x), &ex),
        seq!(
            th,
            cel(TWO, "cz"),
            cel(x, "cz"),
            a1i(&cel(TWO, "cz"), th, "2z"),
            p_xzz,
            "jca"
        ),
        "vn",
        TWO,
        x,
        "divides",
        "syl"
    );
    seq!(th, dvds(TWO, x), ex, wit, bic, "mpbird")
}

/// th -> E. v e. ZZ ( v x. 2 ) = X, from th -> 2 || X.
///
/// `divides` supplies the existential over its own bound variable n, and the
/// readable proof names the obtained integer r and then s. Two obtains from
/// one definition cannot share a name, so the rename is not optional.
fn obtain_even(th: &str, x: &str, v: &str, p_div: &str, p_xzz: &str) -> String {
    let vc = format!("{v} cv");
    let exn = rex(eq(mul(NV, TWO), x), "vn", "cz");
    let exv = rex(eq(mul(&vc, TWO), x), v, "cz");
    let bic = seq!(
        th,
        wa(cel(TWO, "cz"), cel(x, "cz")),
        wb(dvds(TWO, x), &exn),
        seq!(
            th,
            cel(TWO, "cz"),
            cel(x, "cz"),
            a1i(&cel(TWO, "cz"), th, "2z"),
            p_xzz,
            "jca"
        ),
        "vn",
        TWO,
        x,
        "divides",
        "syl"
    );
    let cbv = seq!(
        eq(mul(NV, TWO), x),
        eq(mul(&vc, TWO), x),
        "vn",
        v,
        "cz",
        seq!(
            eq(NV, &vc),
            mul(NV, TWO),
            mul(&vc, TWO),
            x,
            seq!(NV, vc, TWO, "cmul", "oveq1"),
            "eqeq1d"
        ),
        "cbvrexv"
    );
    seq!(
        th,
        exn,
        exv,
        seq!(th, dvds(TWO, x), exn, p_div, bic, "mpbid"),
        cbv,
        "sylib"
    )
}

/// th -> target, discharging the existential the obtain opened.
fn close_scope(
    th: &str,
    x: &str,
    v: &str,
    target: &str,
    p_exv: &str,
    body: &str,
) -> String {
    let vc = format!("{v} cv");
    let eqv = eq(mul(&vc, TWO), x);
    seq!(
        th,
        rex(&eqv, v, "cz"),
        target,
        p_exv,
        seq!(
            th,
            eqv,
            target,
            v,
            "cz",
            seq!(wa(th, cel(&vc, "cz")), eqv, target, body, "ex"),
            "rexlimdva"
        ),
        "mpd"
    )
}

pub fn text() -> String {
    let s = cel(SQ2, "cq");
    let pq = div(PV, QV);
    let psq = exp(PV, TWO);
    let qsq = exp(QV, TWO);
    let rsq = exp(RV, TWO);

    let nod = wn(rex(
        w3a(lt(ONE, DV), dvds(DV, PV), dvds(DV, QV)),
        "vd",
        "cz",
    ));
    let body = w3a(lt(ZERO, QV), eq(SQ2, &pq), &nod);
    let expq = rex(rex(&body, "vq", "cz"), "vp", "cz");

    let chpq = wa(&s, wa(cel(PV, "cz"), cel(QV, "cz")));
    let th1 = wa(&chpq, &body);
    let th2 = wa(wa(&th1, cel(RV, "cz")), eq(mul(RV, TWO), PV));
    let th3 = wa(wa(&th2, cel(SV, "cz")), eq(mul(SV, TWO), QV));

    // --- the three algebra steps --------------------------------------------
    // Step 3.8 is a normalisation with no cited equation, like odd-square's
    // two. Steps 3.3 and 3.10 are the other half of the method: each takes a
    // cited equation and multiplies through by a coefficient, which is ideal
    // membership with one generator. set.mm's ring lemmas are over CC, so the
    // expansion carries the atoms there and the readable text never says so.
    let asqv = exp(AV, TWO);
    let bsqv = exp(BV, TWO);

    // salg2: ( A x. 2 ) ^ 2 = 4 x. ( A ^ 2 ), a bare normalisation.
    let g2 = cel(AV, "cc");
    let g2_a = seq!(g2, "id");
    let g2_asq = seq!(g2, cel(AV, "cc"), cel(&asqv, "cc"), g2_a, AV, "sqcl", "syl");
    let salg2 = seq!(
        g2,
        exp(mul(AV, TWO), TWO),
        mul(&asqv, exp(TWO, TWO)),
        mul(FOUR, &asqv),
        seq!(
            g2,
            wa(cel(AV, "cc"), cel(TWO, "cc")),
            eq(exp(mul(AV, TWO), TWO), mul(&asqv, exp(TWO, TWO))),
            seq!(
                g2,
                cel(AV, "cc"),
                cel(TWO, "cc"),
                g2_a,
                seq!(g2, "2cnd"),
                "jca"
            ),
            AV,
            TWO,
            "sqmul",
            "syl"
        ),
        seq!(
            g2,
            mul(&asqv, exp(TWO, TWO)),
            mul(&asqv, FOUR),
            mul(FOUR, &asqv),
            seq!(
                g2,
                exp(TWO, TWO),
                FOUR,
                asqv,
                "cmul",
                a1i(&eq(exp(TWO, TWO), FOUR), &g2, "sq2"),
                "oveq2d"
            ),
            seq!(
                g2,
                asqv,
                FOUR,
                g2_asq,
                a1i(&cel(FOUR, "cc"), &g2, "4cn"),
                "mulcomd"
            ),
            "eqtrd"
        ),
        "eqtrd"
    );

    // salg3: from 2A^2 = 4B^2 conclude A^2 = 2B^2, by cancelling the 2.
    let g3 = wa(cel(AV, "cc"), cel(BV, "cc"));
    let h3 = eq(mul(TWO, &asqv), mul(FOUR, &bsqv));
    let t3 = wa(&g3, &h3);
    let g3_a = seq!(
        g3,
        cel(AV, "cc"),
        h3,
        seq!(cel(AV, "cc"), cel(BV, "cc"), "simpl"),
        "adantr"
    );
    let g3_b = seq!(
        g3,
        cel(BV, "cc"),
        h3,
        seq!(cel(AV, "cc"), cel(BV, "cc"), "simpr"),
        "adantr"
    );
    let g3_asq = seq!(t3, cel(AV, "cc"), cel(&asqv, "cc"), g3_a, AV, "sqcl", "syl");
    let g3_bsq = seq!(t3, cel(BV, "cc"), cel(&bsqv, "cc"), g3_b, BV, "sqcl", "syl");
    let g3_2bsq = seq!(t3, TWO, bsqv, seq!(t3, "2cnd"), g3_bsq, "mulcld");
    let salg3 = seq!(
        t3,
        eq(mul(TWO, &asqv), mul(TWO, mul(TWO, &bsqv))),
        eq(&asqv, mul(TWO, &bsqv)),
        seq!(
            t3,
            mul(TWO, &asqv),
            mul(FOUR, &bsqv),
            mul(TWO, mul(TWO, &bsqv)),
            seq!(g3, h3, "simpr"),
            seq!(
                t3,
                mul(TWO, mul(TWO, &bsqv)),
                mul(FOUR, &bsqv),
                two_of(&t3, &bsqv, &g3_bsq),
                "eqcomd"
            ),
            "eqtrd"
        ),
        seq!(
            t3,
            asqv,
            mul(TWO, &bsqv),
            TWO,
            g3_asq,
            g3_2bsq,
            seq!(t3, "2cnd"),
            a1i(&ne(TWO, ZERO), &t3, "2ne0"),
            "mulcand"
        ),
        "mpbid"
    );
    let salg3 = seq!(g3, h3, eq(&asqv, mul(TWO, &bsqv)), salg3, "ex");

    // salg1: from ( A / B ) ^ 2 = 2 conclude A^2 = 2B^2, by clearing the
    // divisor.
    let g1 = w3a(cel(AV, "cr"), cel(BV, "cr"), ne(BV, ZERO));
    let h1 = eq(exp(div(AV, BV), TWO), TWO);
    let t1 = wa(&g1, &h1);

    let g1_up = |claim: &str, pf: &str| seq!(g1, claim, h1, pf, "adantr");

    let g1_ar = g1_up(
        &cel(AV, "cr"),
        &seq!(cel(AV, "cr"), cel(BV, "cr"), ne(BV, ZERO), "simp1"),
    );
    let g1_br = g1_up(
        &cel(BV, "cr"),
        &seq!(cel(AV, "cr"), cel(BV, "cr"), ne(BV, ZERO), "simp2"),
    );
    let g1_bne = g1_up(
        &ne(BV, ZERO),
        &seq!(cel(AV, "cr"), cel(BV, "cr"), ne(BV, ZERO), "simp3"),
    );
    let g1_a = seq!(t1, AV, g1_ar, "recnd");
    let g1_b = seq!(t1, BV, g1_br, "recnd");
    let g1_asq = seq!(t1, cel(AV, "cc"), cel(&asqv, "cc"), g1_a, AV, "sqcl", "syl");
    let g1_bsq = seq!(t1, cel(BV, "cc"), cel(&bsqv, "cc"), g1_b, BV, "sqcl", "syl");
    let g1_bsqne = seq!(
        t1,
        ne(&bsqv, ZERO),
        ne(BV, ZERO),
        g1_bne,
        seq!(
            t1,
            cel(BV, "cc"),
            wb(ne(&bsqv, ZERO), ne(BV, ZERO)),
            g1_b,
            BV,
            "sqne0",
            "syl"
        ),
        "mpbird"
    );
    let g1_div = seq!(
        t1,
        exp(div(AV, BV), TWO),
        div(&asqv, &bsqv),
        TWO,
        seq!(
            t1,
            w3a(cel(AV, "cc"), cel(BV, "cc"), ne(BV, ZERO)),
            eq(exp(div(AV, BV), TWO), div(&asqv, &bsqv)),
            seq!(
                t1,
                cel(AV, "cc"),
                cel(BV, "cc"),
                ne(BV, ZERO),
                g1_a,
                g1_b,
                g1_bne,
                "3jca"
            ),
            AV,
            BV,
            "sqdiv",
            "syl"
        ),
        seq!(g1, h1, "simpr"),
        "eqtr3d"
    );
    let salg1 = seq!(
        t1,
        asqv,
        mul(&bsqv, TWO),
        mul(TWO, &bsqv),
        seq!(
            t1,
            mul(&bsqv, TWO),
            asqv,
            seq!(
                t1,
                eq(div(&asqv, &bsqv), TWO),
                eq(mul(&bsqv, TWO), &asqv),
                g1_div,
                seq!(
                    t1,
                    asqv,
                    bsqv,
                    TWO,
                    g1_asq,
                    g1_bsq,
                    seq!(t1, "2cnd"),
                    g1_bsqne,
                    "divmuld"
                ),
                "mpbid"
            ),
            "eqcomd"
        ),
        seq!(t1, bsqv, TWO, g1_bsq, seq!(t1, "2cnd"), "mulcomd"),
        "eqtrd"
    );
    let salg1 = seq!(g1, h1, eq(&asqv, mul(TWO, &bsqv)), salg1, "ex");

    // --- steps 1 and 2, the two facts about the square root -----------------
    let pre = wa(cel(TWO, "cr"), le(ZERO, TWO));
    let p_pre = seq!(cel(TWO, "cr"), le(ZERO, TWO), "2re 0le2 pm3.2i");
    let eq1 = eq(exp(SQ2, TWO), TWO);
    let in2 = cel(SQ2, "cr");
    let step1 = seq!(pre, eq1, p_pre, TWO, "resqrtth", "ax-mp");
    let step2 = seq!(pre, in2, p_pre, TWO, "resqrtcl", "ax-mp");

    // --- what the obtain of step 3.1 puts in scope --------------------------
    let t_p = seq!(s, cel(PV, "cz"), cel(QV, "cz"), body, "simplrl");
    let t_q = seq!(s, cel(PV, "cz"), cel(QV, "cz"), body, "simplrr");
    let t_qpos = seq!(chpq, lt(ZERO, QV), eq(SQ2, &pq), nod, "simpr1");
    let t_eq = seq!(chpq, lt(ZERO, QV), eq(SQ2, &pq), nod, "simpr2");
    let t_nod = seq!(chpq, lt(ZERO, QV), eq(SQ2, &pq), nod, "simpr3");

    let p_pzz = zsq(&th1, PV, &t_p);
    let q_pzz = zsq(&th1, QV, &t_q);
    let p_pr = zre(&th1, PV, &t_p);
    let p_qr = zre(&th1, QV, &t_q);

    // --- step 3.2, substituting the obtained equation into line 1 -----------
    let s32 = seq!(
        th1,
        exp(SQ2, TWO),
        exp(&pq, TWO),
        TWO,
        seq!(th1, SQ2, pq, TWO, "cexp", t_eq, "oveq1d"),
        a1i(&eq1, &th1, &step1),
        "eqtr3d"
    );

    // --- step 3.3, the first algebra step -----------------------------------
    let qne = ne(QV, ZERO);
    let p_qne = seq!(
        th1,
        wa(cel(QV, "cr"), lt(ZERO, QV)),
        qne,
        seq!(th1, cel(QV, "cr"), lt(ZERO, QV), p_qr, t_qpos, "jca"),
        QV,
        "gt0ne0",
        "syl"
    );
    let pre33 = w3a(cel(PV, "cr"), cel(QV, "cr"), &qne);
    let eq33 = eq(&psq, mul(TWO, &qsq));
    let s33 = seq!(
        th1,
        eq(exp(&pq, TWO), TWO),
        eq33,
        s32,
        seq!(
            th1,
            pre33,
            wi(eq(exp(&pq, TWO), TWO), &eq33),
            seq!(
                th1,
                cel(PV, "cr"),
                cel(QV, "cr"),
                qne,
                p_pr,
                p_qr,
                p_qne,
                "3jca"
            ),
            PV,
            QV,
            "salg1",
            "syl"
        ),
        "mpd"
    );

    // --- steps 3.4 and 3.5, p squared is even and so is p -------------------
    let s34 = even_of(&th1, &psq, &qsq, &s33, &q_pzz, &p_pzz);
    let s35 = seq!(
        th1,
        wa(cel(PV, "cz"), dvds(TWO, &psq)),
        dvds(TWO, PV),
        seq!(th1, cel(PV, "cz"), dvds(TWO, &psq), t_p, s34, "jca"),
        PV,
        "evensq",
        "syl"
    );

    // --- step 3.6 opens the second scope ------------------------------------
    let up2_r = cel(RV, "cz");
    let up2_eq = eq(mul(RV, TWO), PV);
    let up2 = [up2_r.as_str(), up2_eq.as_str()];
    let t_r = seq!(th1, cel(RV, "cz"), eq(mul(RV, TWO), PV), "simplr");
    let t_eqr = seq!(wa(&th1, cel(RV, "cz")), eq(mul(RV, TWO), PV), "simpr");

    // --- steps 3.7 to 3.10, the same shape a second time --------------------
    let r2sq = exp(mul(RV, TWO), TWO);
    let s37 = seq!(
        th2,
        PV,
        mul(RV, TWO),
        TWO,
        "cexp",
        seq!(th2, mul(RV, TWO), PV, t_eqr, "eqcomd"),
        "oveq1d"
    );
    let s38 = seq!(
        th2,
        cel(RV, "cc"),
        eq(&r2sq, mul(FOUR, &rsq)),
        zcn(&th2, RV, &t_r),
        RV,
        "salg2",
        "syl"
    );
    let s39 = seq!(
        th2,
        mul(TWO, &qsq),
        psq,
        mul(FOUR, &rsq),
        seq!(
            th2,
            psq,
            mul(TWO, &qsq),
            lift(&eq33, &s33, &th1, &up2),
            "eqcomd"
        ),
        seq!(th2, psq, r2sq, mul(FOUR, &rsq), s37, s38, "eqtrd"),
        "eqtrd"
    );
    let eq310 = eq(&qsq, mul(TWO, &rsq));
    let s310 = seq!(
        th2,
        eq(mul(TWO, &qsq), mul(FOUR, &rsq)),
        eq310,
        s39,
        seq!(
            th2,
            wa(cel(QV, "cc"), cel(RV, "cc")),
            wi(eq(mul(TWO, &qsq), mul(FOUR, &rsq)), &eq310),
            seq!(
                th2,
                cel(QV, "cc"),
                cel(RV, "cc"),
                zcn(&th2, QV, &lift(&cel(QV, "cz"), &t_q, &th1, &up2)),
                zcn(&th2, RV, &t_r),
                "jca"
            ),
            QV,
            RV,
            "salg3",
            "syl"
        ),
        "mpd"
    );

    // --- steps 3.11 and 3.12, and the third scope ---------------------------
    let s311 = even_of(
        &th2,
        &qsq,
        &rsq,
        &s310,
        &zsq(&th2, RV, &t_r),
        &lift(&cel(&qsq, "cz"), &q_pzz, &th1, &up2),
    );
    let s312 = seq!(
        th2,
        wa(cel(QV, "cz"), dvds(TWO, &qsq)),
        dvds(TWO, QV),
        seq!(
            th2,
            cel(QV, "cz"),
            dvds(TWO, &qsq),
            lift(&cel(QV, "cz"), &t_q, &th1, &up2),
            s311,
            "jca"
        ),
        QV,
        "evensq",
        "syl"
    );

    let up3_s = cel(SV, "cz");
    let up3_eq = eq(mul(SV, TWO), QV);
    let up3 = [up3_s.as_str(), up3_eq.as_str()];
    let up23 = [up2[0], up2[1], up3[0], up3[1]];

    // --- steps 3.14 to 3.16, the exhibit ------------------------------------
    // 3.14 and 3.15 change the word for what the kernel has already: `p is
    // even` and `2 divides p` are one formula once
    // def:stdlib/divisibility/even and def:stdlib/divisibility/divides are
    // unfolded, so the two steps carry no kernel move of their own.
    let s314 = lift(&dvds(TWO, PV), &s35, &th1, &up23);
    let s315 = lift(&dvds(TWO, QV), &s312, &th2, &up3);
    let ph16 = w3a(lt(ONE, DV), dvds(DV, PV), dvds(DV, QV));
    let ps16 = w3a(lt(ONE, TWO), dvds(TWO, PV), dvds(TWO, QV));
    let hyp16 = seq!(
        eq(DV, TWO),
        lt(ONE, DV),
        lt(ONE, TWO),
        dvds(DV, PV),
        dvds(TWO, PV),
        dvds(DV, QV),
        dvds(TWO, QV),
        seq!(DV, TWO, ONE, "clt", "breq2"),
        seq!(DV, TWO, PV, "cdvds", "breq1"),
        seq!(DV, TWO, QV, "cdvds", "breq1"),
        "3anbi123d"
    );
    let s316 = seq!(
        th3,
        wa(cel(TWO, "cz"), &ps16),
        rex(&ph16, "vd", "cz"),
        seq!(
            th3,
            cel(TWO, "cz"),
            ps16,
            a1i(&cel(TWO, "cz"), &th3, "2z"),
            seq!(
                th3,
                lt(ONE, TWO),
                dvds(TWO, PV),
                dvds(TWO, QV),
                a1i(&lt(ONE, TWO), &th3, "1lt2"),
                s314,
                s315,
                "3jca"
            ),
            "jca"
        ),
        ph16,
        ps16,
        "vd",
        TWO,
        "cz",
        hyp16,
        "rspcev",
        "syl"
    );

    // --- step 3.17, the join, and the three scopes closing ------------------
    let s317 = seq!(
        th3,
        rex(&ph16, "vd", "cz"),
        wn(&s),
        s316,
        lift(&nod, &t_nod, &th1, &up23),
        "pm2.21dd"
    );
    let close_s = close_scope(
        &th2,
        QV,
        "vs",
        &wn(&s),
        &obtain_even(
            &th2,
            QV,
            "vs",
            &s312,
            &lift(&cel(QV, "cz"), &t_q, &th1, &up2),
        ),
        &s317,
    );
    let close_r = close_scope(
        &th1,
        PV,
        "vr",
        &wn(&s),
        &obtain_even(&th1, PV, "vr", &s35, &t_p),
        &close_s,
    );

    // --- step 3, the contradiction block ------------------------------------
    let body_pq = seq!(chpq, body, wn(&s), close_r, "ex");
    let disch = seq!(
        s,
        body,
        wn(&s),
        "vp",
        "vq",
        "cz",
        "cz",
        body_pq,
        "rexlimdvva"
    );
    let step3 = seq!(
        wi(&s, wn(&s)),
        wn(&s),
        seq!(
            s,
            expq,
            wn(&s),
            seq!(SQ2, "vq", "vp", "vd", "ltrm"),
            disch,
            "mpd"
        ),
        seq!(s, "pm2.01"),
        "ax-mp"
    );

    // --- step 4, the definition of irrational -------------------------------
    let diff = cel(SQ2, seq!("cr", "cq", "cdif"));
    let step4 = seq!(
        diff,
        wa(&in2, wn(&s)),
        seq!(in2, wn(&s), step2, step3, "pm3.2i"),
        SQ2,
        "cr",
        "cq",
        "eldif",
        "mpbir"
    );

    format!(
        r#"$( thm:proofs/sqrt2-irrational/sqrt2-irrational, from
   proofs/sqrt2-irrational.proof, as a Metamath proof.

   Verify with any Metamath verifier, with parity.mm and set.mm in the same
   directory:

       python3 mmverify.py sqrt2.mm

   It was checked against set.mm of 2026-09-19 with mmverify.py, and against a
   copy of that file truncated after oddm1even, which is the last statement it
   uses.

   thm:proofs/sqrt2-irrational/lowest-terms and the proof's three `algebra`
   steps are axioms here. Everything else uses set.mm's own theorems, or
   thm:proofs/sqrt2-irrational/even-square, which parity.mm proves.
$)

$[ parity.mm $]

$( thm:proofs/sqrt2-irrational/lowest-terms, stated as its readable form
   states it. set.mm's nearest statement is qredeu, which gives a unique
   pair in ( ZZ X. NN ) whose gcd is 1; the shapes do not match, and closing
   the gap is a proof of its own. $)
${{
  $d p q r s d n $.  $d p q r s d n A $.
  ltrm $a |- ( A e. QQ -> E. p e. ZZ E. q e. ZZ ( 0 < q /\ A = ( p / q ) /\
               -. E. d e. ZZ ( 1 < d /\ d || p /\ d || q ) ) ) $.
$}}

$( The three `algebra` steps of the readable proof. salg2 is a normalisation
   with no cited equation; salg1 and salg3 each take one cited equation and
   multiply through by a coefficient. $)
salg1 $p |- ( ( A e. RR /\ B e. RR /\ B =/= 0 ) ->
              ( ( ( A / B ) ^ 2 ) = 2 -> ( A ^ 2 ) = ( 2 x. ( B ^ 2 ) ) ) ) $=
  {salg1} $.

salg2 $p |- ( A e. CC -> ( ( A x. 2 ) ^ 2 ) = ( 4 x. ( A ^ 2 ) ) ) $=
  {salg2} $.

salg3 $p |- ( ( A e. CC /\ B e. CC ) ->
              ( ( 2 x. ( A ^ 2 ) ) = ( 4 x. ( B ^ 2 ) ) ->
                ( A ^ 2 ) = ( 2 x. ( B ^ 2 ) ) ) ) $=
  {salg3} $.

${{
  $d p q r s d n $.
  s2irr $p |- ( sqrt ` 2 ) e. ( RR \ QQ ) $=
    {step4} $.
$}}
"#
    )
}

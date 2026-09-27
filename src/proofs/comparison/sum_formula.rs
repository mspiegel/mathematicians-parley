//! thm:proof/sum-formula/sum-formula as a Metamath proof.
//!
//! It is the first proof here with an `induction` and the first with a
//! `fix`, and the first whose definition is recursive. set.mm proves the
//! same statement as `arisum`; citing it would test nothing, so the proof
//! follows the readable one and uses `nnind` with the base and step blocks
//! the text writes.
//!
//! Nothing here is assumed.

use crate::mm::spell::{add, cel, div, eq, fz, mul, ne, summ, w3a, wa};
use crate::seq;

const ONE: &str = "c1";
const TWO: &str = "c2";
const ZERO: &str = "cc0";
const KV: &str = "vk cv";
const YV: &str = "vy cv";
const XV: &str = "vx cv";
const AV: &str = "cA";

fn ai(claim: &str, th: &str, pf: &str) -> String {
    seq!(claim, th, pf, "a1i")
}

/// The claim at `t`: the sum to t is t( t + 1 ) / 2.
fn claim(t: &str) -> String {
    eq(summ(fz(ONE, t), KV, "vk"), div(mul(t, add(t, ONE)), TWO))
}

/// ( x = T -> ( claim(x) <-> claim(T) ) ).
fn instance(t: &str) -> String {
    let at = eq(XV, t);
    let idp = seq!(at, "id");
    let e_sum = seq!(
        at,
        eq(fz(ONE, XV), fz(ONE, t)),
        eq(summ(fz(ONE, XV), KV, "vk"), summ(fz(ONE, t), KV, "vk")),
        seq!(at, XV, t, ONE, "cfz", idp, "oveq2d"),
        seq!(fz(ONE, XV), fz(ONE, t), KV, "vk", "sumeq1"),
        "syl"
    );
    let e_rhs = seq!(
        at,
        mul(XV, add(XV, ONE)),
        mul(t, add(t, ONE)),
        TWO,
        "cdiv",
        seq!(
            at,
            XV,
            t,
            add(XV, ONE),
            add(t, ONE),
            "cmul",
            idp,
            seq!(at, XV, t, ONE, "caddc", idp, "oveq1d"),
            "oveq12d"
        ),
        "oveq1d"
    );
    seq!(
        at,
        summ(fz(ONE, XV), KV, "vk"),
        summ(fz(ONE, t), KV, "vk"),
        div(mul(XV, add(XV, ONE)), TWO),
        div(mul(t, add(t, ONE)), TWO),
        e_sum,
        e_rhs,
        "eqeq12d"
    )
}

pub fn text() -> String {
    let s1 = summ(fz(ONE, ONE), KV, "vk");
    let rhs1 = div(mul(ONE, add(ONE, ONE)), TWO);

    // 1.1  S(1) = 1, the base case: a one-term sum is its term (fsum1).
    let p11 = seq!(
        cel(ONE, "cz"),
        cel(ONE, "cc"),
        eq(&s1, ONE),
        "1z",
        "ax-1cn",
        seq!(KV, ONE, "vk", ONE, seq!(eq(KV, ONE), "id"), "fsum1"),
        "mp2an"
    );

    // 1.2  1 = 1( 1 + 1 ) / 2, the arithmetic step.
    let e_m1 = seq!(
        eq(add(ONE, ONE), TWO),
        eq(mul(ONE, add(ONE, ONE)), mul(ONE, TWO)),
        "1p1e2",
        seq!(add(ONE, ONE), TWO, ONE, "cmul", "oveq2"),
        "ax-mp"
    );
    let e_m2 = seq!(
        cel(TWO, "cc"),
        eq(mul(ONE, TWO), TWO),
        "2cn",
        seq!(TWO, "mullid"),
        "ax-mp"
    );
    let e_num = seq!(
        mul(ONE, add(ONE, ONE)),
        mul(ONE, TWO),
        TWO,
        e_m1,
        e_m2,
        "eqtri"
    );
    let e_div = seq!(
        eq(mul(ONE, add(ONE, ONE)), TWO),
        eq(&rhs1, div(TWO, TWO)),
        e_num,
        seq!(mul(ONE, add(ONE, ONE)), TWO, TWO, "cdiv", "oveq1"),
        "ax-mp"
    );
    let e_dd = seq!(
        cel(TWO, "cc"),
        ne(TWO, ZERO),
        eq(div(TWO, TWO), ONE),
        "2cn",
        "2ne0",
        seq!(TWO, "divid"),
        "mp2an"
    );
    let p12 = seq!(
        rhs1,
        ONE,
        seq!(rhs1, div(TWO, TWO), ONE, e_div, e_dd, "eqtri"),
        "eqcomi"
    );

    // 1.3  the calculation joining them.
    let base = seq!(s1, ONE, rhs1, p11, p12, "eqtri");

    // --- the step block, 1.4 ------------------------------------------------
    let y1 = add(YV, ONE);
    let sy = summ(fz(ONE, YV), KV, "vk");
    let sy1 = summ(fz(ONE, &y1), KV, "vk");
    let ry = div(mul(YV, &y1), TWO);
    let ry1 = div(mul(&y1, add(&y1, ONE)), TWO);
    let ih = eq(&sy, &ry);
    let th = wa(cel(YV, "cn"), &ih);

    let p_y = seq!(cel(YV, "cn"), ih, "simpl");
    let p_ih = seq!(cel(YV, "cn"), ih, "simpr");
    let p_ycn = seq!(th, cel(YV, "cn"), cel(YV, "cc"), p_y, YV, "nncn", "syl");
    let p_1cn = ai(&cel(ONE, "cc"), &th, "ax-1cn");
    let p_2cn = seq!(th, "2cnd");
    let p_2ne = ai(&ne(TWO, ZERO), &th, "2ne0");
    let p_y1cn = seq!(th, YV, ONE, p_ycn, p_1cn, "addcld");
    let p_y2cn = seq!(th, YV, TWO, p_ycn, p_2cn, "addcld");
    let p_yy1 = seq!(th, YV, y1, p_ycn, p_y1cn, "mulcld");
    let p_2y1 = seq!(th, TWO, y1, p_2cn, p_y1cn, "mulcld");

    // 1.4.1  the step: a sum to n + 1 is the sum to n and one more term
    // (fsump1).
    //
    // fsump1 requires that its bound variable not occur in the antecedent,
    // and the induction hypothesis is an equation between sums, so it
    // mentions that variable. The recursion is therefore unfolded before the
    // hypothesis enters, under `y e. NN` alone, and carried in afterwards.
    let nny = cel(YV, "cn");
    let in_fz = wa(&nny, cel(KV, fz(ONE, &y1)));
    let p_uz = seq!(
        nny,
        YV,
        "cn",
        seq!(ONE, "cuz cfv"),
        seq!(nny, "id"),
        "nnuz",
        "eleqtrdi"
    );
    let p_kcc = seq!(
        in_fz,
        cel(KV, "cz"),
        cel(KV, "cc"),
        seq!(
            in_fz,
            cel(KV, fz(ONE, &y1)),
            cel(KV, "cz"),
            seq!(nny, cel(KV, fz(ONE, &y1)), "simpr"),
            seq!(KV, ONE, y1, "elfzelz"),
            "syl"
        ),
        KV,
        "zcn",
        "syl"
    );
    let p141 = seq!(
        nny,
        eq(&sy1, add(&sy, &y1)),
        ih,
        seq!(
            nny,
            KV,
            y1,
            "vk",
            ONE,
            YV,
            p_uz,
            p_kcc,
            seq!(eq(KV, &y1), "id"),
            "fsump1"
        ),
        "adantr"
    );

    // 1.4.2  the induction hypothesis goes in.
    let p142 = seq!(th, sy, ry, y1, "caddc", p_ih, "oveq1d");

    // 1.4.3  the algebra step, proved in the direction the identity runs and
    // then turned round, as the readable line states it the other way.
    let e_y2 = seq!(
        th,
        add(&y1, ONE),
        add(YV, add(ONE, ONE)),
        add(YV, TWO),
        seq!(th, YV, ONE, ONE, p_ycn, p_1cn, p_1cn, "addassd"),
        seq!(
            th,
            add(ONE, ONE),
            TWO,
            YV,
            "caddc",
            ai(&eq(add(ONE, ONE), TWO), &th, "1p1e2"),
            "oveq2d"
        ),
        "eqtrd"
    );
    let e_dir = seq!(
        th,
        w3a(cel(YV, "cc"), cel(TWO, "cc"), cel(&y1, "cc")),
        eq(mul(add(YV, TWO), &y1), add(mul(YV, &y1), mul(TWO, &y1))),
        seq!(
            th,
            cel(YV, "cc"),
            cel(TWO, "cc"),
            cel(&y1, "cc"),
            p_ycn,
            p_2cn,
            p_y1cn,
            "3jca"
        ),
        YV,
        TWO,
        y1,
        "adddir",
        "syl"
    );
    let e_top = seq!(
        th,
        mul(&y1, add(&y1, ONE)),
        mul(&y1, add(YV, TWO)),
        add(mul(YV, &y1), mul(TWO, &y1)),
        seq!(th, add(&y1, ONE), add(YV, TWO), y1, "cmul", e_y2, "oveq2d"),
        seq!(
            th,
            mul(&y1, add(YV, TWO)),
            mul(add(YV, TWO), &y1),
            add(mul(YV, &y1), mul(TWO, &y1)),
            seq!(th, y1, add(YV, TWO), p_y1cn, p_y2cn, "mulcomd"),
            e_dir,
            "eqtrd"
        ),
        "eqtrd"
    );
    let e_dd = seq!(
        th,
        w3a(
            cel(mul(YV, &y1), "cc"),
            cel(mul(TWO, &y1), "cc"),
            wa(cel(TWO, "cc"), ne(TWO, ZERO))
        ),
        eq(
            div(add(mul(YV, &y1), mul(TWO, &y1)), TWO),
            add(div(mul(YV, &y1), TWO), div(mul(TWO, &y1), TWO))
        ),
        seq!(
            th,
            cel(mul(YV, &y1), "cc"),
            cel(mul(TWO, &y1), "cc"),
            wa(cel(TWO, "cc"), ne(TWO, ZERO)),
            p_yy1,
            p_2y1,
            seq!(th, cel(TWO, "cc"), ne(TWO, ZERO), p_2cn, p_2ne, "jca"),
            "3jca"
        ),
        mul(YV, &y1),
        mul(TWO, &y1),
        TWO,
        "divdir",
        "syl"
    );
    let e_can = seq!(
        th,
        w3a(cel(&y1, "cc"), cel(TWO, "cc"), ne(TWO, ZERO)),
        eq(div(mul(TWO, &y1), TWO), &y1),
        seq!(
            th,
            cel(&y1, "cc"),
            cel(TWO, "cc"),
            ne(TWO, ZERO),
            p_y1cn,
            p_2cn,
            p_2ne,
            "3jca"
        ),
        y1,
        TWO,
        "divcan3",
        "syl"
    );
    let p143 = seq!(
        th,
        ry1,
        add(&ry, &y1),
        seq!(
            th,
            ry1,
            add(&ry, div(mul(TWO, &y1), TWO)),
            add(&ry, &y1),
            seq!(
                th,
                ry1,
                div(add(mul(YV, &y1), mul(TWO, &y1)), TWO),
                add(&ry, div(mul(TWO, &y1), TWO)),
                seq!(
                    th,
                    mul(&y1, add(&y1, ONE)),
                    add(mul(YV, &y1), mul(TWO, &y1)),
                    TWO,
                    "cdiv",
                    e_top,
                    "oveq1d"
                ),
                e_dd,
                "eqtrd"
            ),
            seq!(
                th,
                div(mul(TWO, &y1), TWO),
                y1,
                ry,
                "caddc",
                e_can,
                "oveq2d"
            ),
            "eqtrd"
        ),
        "eqcomd"
    );

    // 1.4.4  the calculation.
    let p144 = seq!(
        th,
        sy1,
        add(&sy, &y1),
        ry1,
        p141,
        seq!(th, add(&sy, &y1), add(&ry, &y1), ry1, p142, p143, "eqtrd"),
        "eqtrd"
    );
    let step = seq!(cel(YV, "cn"), ih, eq(&sy1, &ry1), p144, "ex");

    // --- step 1, the induction itself ---------------------------------------
    // nnind wants the claim at four instances of its variable, and the
    // readable line never writes any of them: the text says only "induction
    // on n starting at 1". Each is built by congruence out of x = T.
    let proof = seq!(
        claim(XV),
        claim(ONE),
        claim(YV),
        claim(&y1),
        claim(AV),
        "vx",
        "vy",
        AV,
        instance(ONE),
        instance(YV),
        instance(&y1),
        instance(AV),
        base,
        step,
        "nnind"
    );

    format!(
        r#"$( thm:proof/sum-formula/sum-formula, from proof/sum-formula.proof, as a
   Metamath proof.

   Verify with any Metamath verifier, with set.mm in the same directory:

       python3 mmverify.py sum-formula.mm

   It was checked against set.mm of 2026-09-19 with mmverify.py and with the
   metamath program, and against a copy of that file truncated after
   oddm1even.

   set.mm proves this statement as arisum. It is not cited; the proof follows
   the readable one. Nothing here is assumed.
$)

$[ set.mm $]

${{
  $d k x y A $.
  sumform $p |- ( A e. NN ->
      sum_ k e. ( 1 ... A ) k = ( ( A x. ( A + 1 ) ) / 2 ) ) $=
    {proof} $.
$}}
"#
    )
}

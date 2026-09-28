//! Step 3 of thm:proofs/bezout/least-combination-divides as a Metamath proof.
//!
//! It is the one `algebra` step in the corpus whose coefficients are not
//! constants. The step combines three cited equations with coefficients -1,
//! 1 and -q, where every other step in the corpus either cites nothing or
//! uses constant coefficients, so it is the case that decides whether
//! `algebra` has one lemma order or needs a search.
//!
//! It does not: the order the five smaller steps follow carries this one
//! too. What is new is the price of the hypotheses. Ten atoms all have to be
//! in CC, and the proof carries that conjunction into every line, which is
//! most of its size.

use crate::mm::spell::{add, cel, eq, mul, sub, w3a, wa, wb};
use crate::seq;

const A: &str = "cA";
const B: &str = "cB";
const C: &str = "cC";
const D: &str = "cD";
const U: &str = "cU";
const V: &str = "cV";
const X: &str = "cX";
const Y: &str = "cY";
const Q: &str = "cQ";
const R: &str = "cR";
const ATOMS: [&str; 10] = [A, B, C, D, U, V, X, Y, Q, R];

/// The parts joined into a left-nested conjunction.
fn conj(parts: &[String]) -> String {
    let mut out = parts[0].clone();
    for p in &parts[1..] {
        out = wa(&out, p);
    }
    out
}

/// GH -> MEM[i], by walking out of the left-nested conjunction.
fn pick(mem: &[String], i: usize) -> String {
    let (mut pf, mut k) = if i == 0 {
        (seq!(mem[0], mem[1], "simpl"), 2)
    } else {
        (seq!(conj(&mem[..i]), mem[i], "simpr"), i + 1)
    };
    while k < mem.len() {
        pf = seq!(
            conj(&mem[..k + 1]),
            conj(&mem[..k]),
            mem[i],
            seq!(conj(&mem[..k]), mem[k], "simpl"),
            pf,
            "syl"
        );
        k += 1;
    }
    pf
}

/// The text of a left-nested conjunction, as set.mm writes it.
fn cj(parts: &[String]) -> String {
    let mut out = parts[0].clone();
    for p in &parts[1..] {
        out = format!("( {out} /\\ {p} )");
    }
    out
}

pub fn text() -> String {
    let mem: Vec<String> = ATOMS.iter().map(|a| cel(a, "cc")).collect();
    let gh = conj(&mem);

    let e1 = eq(C, add(mul(Q, D), R)); // from line 2
    let e2 = eq(C, add(mul(A, U), mul(B, V))); // H9
    let e3 = eq(D, add(mul(A, X), mul(B, Y))); // H10
    let hyp = w3a(&e1, &e2, &e3);
    let th = wa(&gh, &hyp);

    let in_cc: Vec<String> = ATOMS
        .iter()
        .enumerate()
        .map(|(i, a)| seq!(gh, cel(a, "cc"), hyp, pick(&mem, i), "adantr"))
        .collect();
    let cc = |a: &str| -> &str {
        let i = ATOMS.iter().position(|x| *x == a).expect("an atom");
        &in_cc[i]
    };

    let prod = |a: &str, b: &str| seq!(th, a, b, cc(a), cc(b), "mulcld");

    let h1 = seq!(gh, e1, e2, e3, "simpr1");
    let h2 = seq!(gh, e1, e2, e3, "simpr2");
    let h3 = seq!(gh, e1, e2, e3, "simpr3");

    let au = mul(A, U);
    let bv = mul(B, V);
    let ax = mul(A, X);
    let by = mul(B, Y);
    let qx = mul(Q, X);
    let qy = mul(Q, Y);
    let qd = mul(Q, D);
    let p_au = prod(A, U);
    let p_bv = prod(B, V);
    let p_ax = prod(A, X);
    let p_by = prod(B, Y);
    let p_qx = prod(Q, X);
    let p_qy = prod(Q, Y);
    let p_qd = prod(Q, D);
    let p_aqx = seq!(th, A, qx, cc(A), p_qx, "mulcld");
    let p_bqy = seq!(th, B, qy, cc(B), p_qy, "mulcld");

    // R = C - ( Q x. D ), from C = ( Q x. D ) + R.
    let back = seq!(
        th,
        sub(C, &qd),
        R,
        seq!(
            th,
            eq(sub(C, &qd), R),
            eq(add(&qd, R), C),
            seq!(th, C, add(&qd, R), h1, "eqcomd"),
            seq!(
                th,
                w3a(cel(C, "cc"), cel(&qd, "cc"), cel(R, "cc")),
                wb(eq(sub(C, &qd), R), eq(add(&qd, R), C)),
                seq!(
                    th,
                    cel(C, "cc"),
                    cel(&qd, "cc"),
                    cel(R, "cc"),
                    cc(C),
                    p_qd,
                    cc(R),
                    "3jca"
                ),
                C,
                qd,
                R,
                "subadd",
                "syl"
            ),
            "mpbird"
        ),
        "eqcomd"
    );

    // and the two cited equations go in.
    let sub_in = seq!(
        th,
        C,
        add(&au, &bv),
        qd,
        mul(Q, add(&ax, &by)),
        "cmin",
        h2,
        seq!(th, D, add(&ax, &by), Q, "cmul", h3, "oveq2d"),
        "oveq12d"
    );

    // Q x. ( AX + BY ) = A x. ( Q x. X ) + B x. ( Q x. Y )
    let distr = seq!(
        th,
        w3a(cel(Q, "cc"), cel(&ax, "cc"), cel(&by, "cc")),
        eq(mul(Q, add(&ax, &by)), add(mul(Q, &ax), mul(Q, &by))),
        seq!(
            th,
            cel(Q, "cc"),
            cel(&ax, "cc"),
            cel(&by, "cc"),
            cc(Q),
            p_ax,
            p_by,
            "3jca"
        ),
        Q,
        ax,
        by,
        "adddi",
        "syl"
    );

    // TH -> ( f x. ( g x. h ) ) = ( g x. ( f x. h ) ).
    let swap = |f: &str, g: &str, h: &str, p_f: &str, p_g: &str, p_h: &str| {
        seq!(
            th,
            w3a(cel(f, "cc"), cel(g, "cc"), cel(h, "cc")),
            eq(mul(f, mul(g, h)), mul(g, mul(f, h))),
            seq!(
                th,
                cel(f, "cc"),
                cel(g, "cc"),
                cel(h, "cc"),
                p_f,
                p_g,
                p_h,
                "3jca"
            ),
            f,
            g,
            h,
            "mul12",
            "syl"
        )
    };

    let regroup = seq!(
        th,
        mul(Q, &ax),
        mul(A, &qx),
        mul(Q, &by),
        mul(B, &qy),
        "caddc",
        swap(Q, A, X, cc(Q), cc(A), cc(X)),
        swap(Q, B, Y, cc(Q), cc(B), cc(Y)),
        "oveq12d"
    );
    let qterm = seq!(
        th,
        mul(Q, add(&ax, &by)),
        add(mul(Q, &ax), mul(Q, &by)),
        add(mul(A, &qx), mul(B, &qy)),
        distr,
        regroup,
        "eqtrd"
    );

    // ( AU + BV ) - ( A(QX) + B(QY) ) = ( AU - A(QX) ) + ( BV - B(QY) )
    let split = seq!(
        th,
        wa(
            wa(cel(&au, "cc"), cel(&bv, "cc")),
            wa(cel(mul(A, &qx), "cc"), cel(mul(B, &qy), "cc"))
        ),
        eq(
            sub(add(&au, &bv), add(mul(A, &qx), mul(B, &qy))),
            add(sub(&au, mul(A, &qx)), sub(&bv, mul(B, &qy)))
        ),
        seq!(
            th,
            wa(cel(&au, "cc"), cel(&bv, "cc")),
            wa(cel(mul(A, &qx), "cc"), cel(mul(B, &qy), "cc")),
            seq!(th, cel(&au, "cc"), cel(&bv, "cc"), p_au, p_bv, "jca"),
            seq!(
                th,
                cel(mul(A, &qx), "cc"),
                cel(mul(B, &qy), "cc"),
                p_aqx,
                p_bqy,
                "jca"
            ),
            "jca"
        ),
        au,
        bv,
        mul(A, &qx),
        mul(B, &qy),
        "addsub4",
        "syl"
    );

    // TH -> ( ( f x. g ) - ( f x. h ) ) = ( f x. ( g - h ) ).
    let factor = |f: &str, g: &str, h: &str, p_g: &str, p_h: &str| {
        seq!(
            th,
            mul(f, sub(g, h)),
            sub(mul(f, g), mul(f, h)),
            seq!(
                th,
                w3a(cel(f, "cc"), cel(g, "cc"), cel(h, "cc")),
                eq(mul(f, sub(g, h)), sub(mul(f, g), mul(f, h))),
                seq!(
                    th,
                    cel(f, "cc"),
                    cel(g, "cc"),
                    cel(h, "cc"),
                    cc(f),
                    p_g,
                    p_h,
                    "3jca"
                ),
                f,
                g,
                h,
                "subdi",
                "syl"
            ),
            "eqcomd"
        )
    };

    let target = add(mul(A, sub(U, &qx)), mul(B, sub(V, &qy)));
    let refactor = seq!(
        th,
        sub(&au, mul(A, &qx)),
        mul(A, sub(U, &qx)),
        sub(&bv, mul(B, &qy)),
        mul(B, sub(V, &qy)),
        "caddc",
        factor(A, U, &qx, cc(U), &p_qx),
        factor(B, V, &qy, cc(V), &p_qy),
        "oveq12d"
    );

    let rhs0 = sub(add(&au, &bv), mul(Q, add(&ax, &by)));
    let rhs1 = sub(add(&au, &bv), add(mul(A, &qx), mul(B, &qy)));
    let rhs2 = add(sub(&au, mul(A, &qx)), sub(&bv, mul(B, &qy)));
    let norm = seq!(
        th,
        rhs0,
        rhs2,
        target,
        seq!(
            th,
            rhs0,
            rhs1,
            rhs2,
            seq!(
                th,
                mul(Q, add(&ax, &by)),
                add(mul(A, &qx), mul(B, &qy)),
                add(&au, &bv),
                "cmin",
                qterm,
                "oveq2d"
            ),
            split,
            "eqtrd"
        ),
        refactor,
        "eqtrd"
    );

    let proof = seq!(
        th,
        R,
        sub(C, &qd),
        target,
        back,
        seq!(th, sub(C, &qd), rhs0, target, sub_in, norm, "eqtrd"),
        "eqtrd"
    );
    let proof = seq!(gh, hyp, eq(R, &target), proof, "ex");

    let gh_txt = cj(&"ABCDUVXYQR"
        .chars()
        .map(|n| format!("{n} e. CC"))
        .collect::<Vec<_>>());
    let hyp_txt = "( C = ( ( Q x. D ) + R ) /\\ C = ( ( A x. U ) + ( B x. V ) ) \
                   /\\ D = ( ( A x. X ) + ( B x. Y ) ) )";
    let out_txt = "R = ( ( A x. ( U - ( Q x. X ) ) ) + ( B x. ( V - ( Q x. Y ) ) ) )";

    format!(
        r#"$( Step 3 of thm:proofs/bezout/least-combination-divides, from
   proofs/bezout.proof, as a Metamath proof.

   Verify with any Metamath verifier, with set.mm in the same directory:

       python3 mmverify.py algebra.mm

   It was checked against set.mm of 2026-09-19 with mmverify.py and with the
   metamath program, and against a copy of that file truncated after
   oddm1even.

   Nothing here is assumed.
$)

$[ set.mm $]

$( r = a ( u - q x0 ) + b ( v - q y0 ), from c = q d + r, c = a u + b v and
   d = a x0 + b y0. The three cited equations enter with coefficients -1, 1
   and -q. $)
balg1 $p |- ( {gh_txt} -> ( {hyp_txt} -> {out_txt} ) ) $=
  {proof} $.
"#
    )
}

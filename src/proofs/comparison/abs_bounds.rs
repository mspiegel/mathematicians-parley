//! thm:proof/triangle-inequality/abs-bounds as a Metamath proof.
//!
//! It is the first proof here with a `cases` block, which completes the four
//! block forms, and the first with any `inequalities` step expanded.
//!
//! Nothing here is assumed.

use crate::mm::spell::{cel, eq, le, lt, neg, wa, wi, wo};
use crate::seq;

const X: &str = "cX";
const ZERO: &str = "cc0";

fn ai(claim: &str, th: &str, pf: &str) -> String {
    seq!(claim, th, pf, "a1i")
}

pub fn text() -> String {
    let ph = cel(X, "cr");
    let absx = seq!(X, "cabs cfv");
    let negx = neg(X);
    let concl = wa(le(X, &absx), le(&negx, &absx));

    // --- step 1, every real is nonnegative or negative ----------------------
    let disj = wo(le(ZERO, X), lt(X, ZERO));
    let p1 = seq!(
        ph,
        wa(cel(ZERO, "cr"), cel(X, "cr")),
        disj,
        seq!(
            ph,
            cel(ZERO, "cr"),
            cel(X, "cr"),
            ai(&cel(ZERO, "cr"), &ph, "0re"),
            seq!(ph, "id"),
            "jca"
        ),
        ZERO,
        X,
        "lelttric",
        "syl"
    );

    // --- the first case, x >= 0 ---------------------------------------------
    // The case assumption and the theorem hypothesis together are exactly
    // what absid wants, so the definition step is the bare lemma.
    let c1 = wa(&ph, le(ZERO, X));
    let c1_x = seq!(ph, le(ZERO, X), "simpl");
    let c1_ge = seq!(ph, le(ZERO, X), "simpr");
    let p21 = seq!(X, "absid");
    let p21r = seq!(c1, absx, X, p21, "eqcomd");

    let p22 = seq!(
        c1,
        X,
        X,
        absx,
        "cle",
        seq!(c1, cel(X, "cr"), le(X, X), c1_x, X, "leid", "syl"),
        p21r,
        "breqtrd"
    );
    let c1_neg = seq!(
        c1,
        cel(X, "cr"),
        cel(&negx, "cr"),
        c1_x,
        X,
        "renegcl",
        "syl"
    );
    let p23 = seq!(
        c1,
        negx,
        X,
        absx,
        "cle",
        seq!(
            c1,
            negx,
            ZERO,
            X,
            c1_neg,
            ai(&cel(ZERO, "cr"), &c1, "0re"),
            c1_x,
            seq!(
                c1,
                le(ZERO, X),
                le(&negx, ZERO),
                c1_ge,
                seq!(
                    c1,
                    cel(X, "cr"),
                    seq!(le(ZERO, X), le(&negx, ZERO), "wb"),
                    c1_x,
                    X,
                    "le0neg2",
                    "syl"
                ),
                "mpbid"
            ),
            c1_ge,
            "letrd"
        ),
        p21r,
        "breqtrd"
    );
    let case1 = seq!(c1, le(X, &absx), le(&negx, &absx), p22, p23, "jca");

    // --- the second case, x < 0 ---------------------------------------------
    // Here the assumption is strict and absnid wants a non-strict one, so the
    // definition step costs a step the text does not write.
    let c2 = wa(&ph, lt(X, ZERO));
    let c2_x = seq!(ph, lt(X, ZERO), "simpl");
    let c2_lt = seq!(ph, lt(X, ZERO), "simpr");
    let c2_lex = seq!(
        c2,
        lt(X, ZERO),
        le(X, ZERO),
        c2_lt,
        seq!(
            c2,
            wa(cel(X, "cr"), cel(ZERO, "cr")),
            wi(lt(X, ZERO), le(X, ZERO)),
            seq!(
                c2,
                cel(X, "cr"),
                cel(ZERO, "cr"),
                c2_x,
                ai(&cel(ZERO, "cr"), &c2, "0re"),
                "jca"
            ),
            X,
            ZERO,
            "ltle",
            "syl"
        ),
        "mpd"
    );
    let p25 = seq!(
        c2,
        wa(cel(X, "cr"), le(X, ZERO)),
        eq(&absx, &negx),
        seq!(c2, cel(X, "cr"), le(X, ZERO), c2_x, c2_lex, "jca"),
        X,
        "absnid",
        "syl"
    );
    let p25r = seq!(c2, absx, negx, p25, "eqcomd");
    let c2_neg = seq!(
        c2,
        cel(X, "cr"),
        cel(&negx, "cr"),
        c2_x,
        X,
        "renegcl",
        "syl"
    );

    let p26 = seq!(
        c2,
        negx,
        negx,
        absx,
        "cle",
        seq!(
            c2,
            cel(&negx, "cr"),
            le(&negx, &negx),
            c2_neg,
            negx,
            "leid",
            "syl"
        ),
        p25r,
        "breqtrd"
    );
    let p27 = seq!(
        c2,
        X,
        negx,
        absx,
        "cle",
        seq!(
            c2,
            X,
            ZERO,
            negx,
            c2_x,
            ai(&cel(ZERO, "cr"), &c2, "0re"),
            c2_neg,
            c2_lex,
            seq!(
                c2,
                le(X, ZERO),
                le(ZERO, &negx),
                c2_lex,
                seq!(
                    c2,
                    cel(X, "cr"),
                    seq!(le(X, ZERO), le(ZERO, &negx), "wb"),
                    c2_x,
                    X,
                    "le0neg1",
                    "syl"
                ),
                "mpbid"
            ),
            "letrd"
        ),
        p25r,
        "breqtrd"
    );
    // 2.8 joins 2.6 and 2.7 in that order, but the theorem states the
    // conjuncts the other way round, so the pair is built in the
    // conclusion's order.
    let case2 = seq!(c2, le(X, &absx), le(&negx, &absx), p27, p26, "jca");

    // --- step 2, the cases block closing ------------------------------------
    let proof = seq!(
        ph,
        le(ZERO, X),
        concl,
        lt(X, ZERO),
        case1,
        case2,
        p1,
        "mpjaodan"
    );

    format!(
        r#"$( thm:proof/triangle-inequality/abs-bounds, from
   proof/triangle-inequality.proof, as a Metamath proof.

   Verify with any Metamath verifier, with set.mm in the same directory:

       python3 mmverify.py abs-bounds.mm

   It was checked against set.mm of 2026-09-19 with mmverify.py and with the
   metamath program, and against a copy of that file truncated after
   oddm1even.

   Nothing here is assumed.
$)

$[ set.mm $]

absbnd $p |- ( X e. RR ->
    ( X <_ ( abs ` X ) /\ -u X <_ ( abs ` X ) ) ) $=
  {proof} $.
"#
    )
}

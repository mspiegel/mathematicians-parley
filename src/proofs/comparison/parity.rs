//! Two theorems of proof/sqrt2-irrational as Metamath proofs:
//! thm:proof/sqrt2-irrational/odd-square and
//! thm:proof/sqrt2-irrational/even-square.
//!
//! A readable theorem's hypotheses become the antecedent of an implication
//! rather than Metamath essential hypotheses. Even-square cites odd-square
//! inside a contradiction block, where nothing is a proved statement and
//! only an implication can be applied.
//!
//! The two `algebra` steps are proved rather than assumed. Both are
//! normalisations with no cited equation, and the second reuses the first's
//! pieces, which is the fixed lemma order METHODS.md asks `algebra` for.

use crate::mm::spell::{add, cel, dvds, eq, exp, mul, w3a, wa, wi, wn, wo};
use crate::seq;

const A: &str = "cA";
const TWO: &str = "c2";
const ONE: &str = "c1";
const FOUR: &str = "c4";
/// The bound n, as a class.
const NV: &str = "vn cv";
/// The witness variable.
const MV: &str = "vm cv";
const NC: &str = "cN";

fn in_zz(a: impl AsRef<str>) -> String {
    cel(a, "cz")
}

fn in_cc(a: impl AsRef<str>) -> String {
    cel(a, "cc")
}

pub fn text() -> String {
    let nsq = exp(NV, TWO);
    let asq = exp(A, TWO);
    // 2n^2 + 2n
    let w = add(mul(TWO, &nsq), mul(TWO, NV));

    // ( 2n + 1 ) = A
    let eqn = eq(add(mul(TWO, NV), ONE), A);
    let exn = seq!(eqn, "vn cz wrex");
    let odd_a = wn(dvds(TWO, A));
    let odd_asq = wn(dvds(TWO, &asq));

    // odd-square's two hypotheses, conjoined, and the scope the obtain opens
    let ch = wa(in_zz(A), &odd_a);
    let chn = wa(&ch, in_zz(NV));
    let th = wa(&chn, &eqn);

    // --- the two algebra steps ----------------------------------------------
    // Both are normalisations with no cited equation, which is what twelve
    // of the corpus's seventeen algebra steps are. set.mm's ring lemmas are
    // over CC, so the expansion carries the atom there and the readable text
    // never says so.

    // the one hypothesis an identity needs
    let alg = in_cc(NC);
    let ncsq = exp(NC, TWO);
    let tnc = mul(TWO, NC);

    let ai = |claim: &str, pf: &str| seq!(claim, alg, pf, "a1i");

    let a_n = seq!(alg, "id");
    let a_2 = ai(&in_cc(TWO), "2cn");
    let a_1 = ai(&in_cc(ONE), "ax-1cn");
    let a_tn = seq!(alg, TWO, NC, a_2, a_n, "mulcld");
    let a_nsq = seq!(alg, in_cc(NC), in_cc(&ncsq), a_n, NC, "sqcl", "syl");

    // ALG -> ( 2 x. ( 2 x. X ) ) = ( 4 x. X ).
    //
    // Twice-two is the only numeral fact these identities need, and it is
    // reached the same way each time: associate, then replace the product of
    // numerals. Three of the five uses below are this one call.
    let double = |x: &str, p_x: &str| {
        let assoc = seq!(
            alg,
            mul(mul(TWO, TWO), x),
            mul(TWO, mul(TWO, x)),
            seq!(
                alg,
                w3a(in_cc(TWO), in_cc(TWO), in_cc(x)),
                eq(mul(mul(TWO, TWO), x), mul(TWO, mul(TWO, x))),
                seq!(alg, in_cc(TWO), in_cc(TWO), in_cc(x), a_2, a_2, p_x, "3jca"),
                TWO,
                TWO,
                x,
                "mulass",
                "syl"
            ),
            "eqcomd"
        );
        let numeral = seq!(
            alg,
            mul(TWO, TWO),
            FOUR,
            x,
            "cmul",
            ai(&eq(mul(TWO, TWO), FOUR), "2t2e4"),
            "oveq1d"
        );
        seq!(
            alg,
            mul(TWO, mul(TWO, x)),
            mul(mul(TWO, TWO), x),
            mul(FOUR, x),
            assoc,
            numeral,
            "eqtrd"
        )
    };

    // oalg1, the square of a sum. binom2 gets close, and the three terms it
    // leaves are what the rest of this settles.
    let b1 = exp(&tnc, TWO);
    let b2 = mul(TWO, mul(&tnc, ONE));
    let b3 = exp(ONE, TWO);
    let binom = add(add(&b1, &b2), &b3);
    let a_binom = seq!(
        alg,
        wa(in_cc(&tnc), in_cc(ONE)),
        eq(exp(add(&tnc, ONE), TWO), &binom),
        seq!(alg, in_cc(&tnc), in_cc(ONE), a_tn, a_1, "jca"),
        tnc,
        ONE,
        "binom2",
        "syl"
    );
    let a_first = seq!(
        alg,
        b1,
        mul(exp(TWO, TWO), &ncsq),
        mul(FOUR, &ncsq),
        seq!(
            alg,
            wa(in_cc(TWO), in_cc(NC)),
            eq(&b1, mul(exp(TWO, TWO), &ncsq)),
            seq!(alg, in_cc(TWO), in_cc(NC), a_2, a_n, "jca"),
            TWO,
            NC,
            "sqmul",
            "syl"
        ),
        seq!(
            alg,
            exp(TWO, TWO),
            FOUR,
            ncsq,
            "cmul",
            ai(&eq(exp(TWO, TWO), FOUR), "sq2"),
            "oveq1d"
        ),
        "eqtrd"
    );
    let a_second = seq!(
        alg,
        b2,
        mul(TWO, &tnc),
        mul(FOUR, NC),
        seq!(
            alg,
            mul(&tnc, ONE),
            tnc,
            TWO,
            "cmul",
            seq!(
                alg,
                in_cc(&tnc),
                eq(mul(&tnc, ONE), &tnc),
                a_tn,
                tnc,
                "mulrid",
                "syl"
            ),
            "oveq2d"
        ),
        double(NC, &a_n),
        "eqtrd"
    );
    let expanded = add(add(mul(FOUR, &ncsq), mul(FOUR, NC)), ONE);
    let oalg1 = seq!(
        alg,
        exp(add(&tnc, ONE), TWO),
        binom,
        expanded,
        a_binom,
        seq!(
            alg,
            add(&b1, &b2),
            add(mul(FOUR, &ncsq), mul(FOUR, NC)),
            b3,
            ONE,
            "caddc",
            seq!(
                alg,
                b1,
                mul(FOUR, &ncsq),
                b2,
                mul(FOUR, NC),
                "caddc",
                a_first,
                a_second,
                "oveq12d"
            ),
            ai(&eq(&b3, ONE), "sq1"),
            "oveq12d"
        ),
        "eqtrd"
    );

    // oalg2, the regrouping. Distribute, then halve each term back.
    let wc = add(mul(TWO, &ncsq), mul(TWO, NC));
    let a_distr = seq!(
        alg,
        w3a(in_cc(TWO), in_cc(mul(TWO, &ncsq)), in_cc(mul(TWO, NC))),
        eq(
            mul(TWO, &wc),
            add(mul(TWO, mul(TWO, &ncsq)), mul(TWO, mul(TWO, NC)))
        ),
        seq!(
            alg,
            in_cc(TWO),
            in_cc(mul(TWO, &ncsq)),
            in_cc(mul(TWO, NC)),
            a_2,
            seq!(alg, TWO, ncsq, a_2, a_nsq, "mulcld"),
            seq!(alg, TWO, NC, a_2, a_n, "mulcld"),
            "3jca"
        ),
        TWO,
        mul(TWO, &ncsq),
        mul(TWO, NC),
        "adddi",
        "syl"
    );
    let a_inner = seq!(
        alg,
        mul(TWO, &wc),
        add(mul(TWO, mul(TWO, &ncsq)), mul(TWO, mul(TWO, NC))),
        add(mul(FOUR, &ncsq), mul(FOUR, NC)),
        a_distr,
        seq!(
            alg,
            mul(TWO, mul(TWO, &ncsq)),
            mul(FOUR, &ncsq),
            mul(TWO, mul(TWO, NC)),
            mul(FOUR, NC),
            "caddc",
            double(&ncsq, &a_nsq),
            double(NC, &a_n),
            "oveq12d"
        ),
        "eqtrd"
    );
    let oalg2 = seq!(
        alg,
        add(mul(FOUR, &ncsq), mul(FOUR, NC)),
        mul(TWO, &wc),
        ONE,
        "caddc",
        seq!(
            alg,
            mul(TWO, &wc),
            add(mul(FOUR, &ncsq), mul(FOUR, NC)),
            a_inner,
            "eqcomd"
        ),
        "oveq1d"
    );

    // --- odd-square ---------------------------------------------------------

    // Step 1, the obtain. The scope is opened by proving the rest of the
    // proof out of TH, so what the later steps get is each conjunct of TH in
    // turn.
    let p_chn = seq!(chn, eqn, "simpl");
    let p_n = seq!(th, ch, in_zz(NV), p_chn, "simprd");
    let p_ch = seq!(th, ch, in_zz(NV), p_chn, "simpld");
    let p_azz = seq!(th, in_zz(A), odd_a, p_ch, "simpld");
    let p_eqn = seq!(chn, eqn, "simpr");
    let p_ncc = seq!(th, in_zz(NV), in_cc(NV), p_n, NV, "zcn syl");

    let sq = exp(add(mul(TWO, NV), ONE), TWO);
    let mid = add(add(mul(FOUR, &nsq), mul(FOUR, NV)), ONE);
    let target = add(mul(TWO, &w), ONE);

    // Steps 3 and 4, the two algebra identities, each needing n in CC.
    let alg1 = seq!(th, in_cc(NV), eq(&sq, &mid), p_ncc, NV, "oalg1 syl");
    let alg2 = seq!(th, in_cc(NV), eq(&mid, &target), p_ncc, NV, "oalg2 syl");

    // Step 5, the calculation: two equalities chained by transitivity.
    let calc = seq!(th, sq, mid, target, alg1, alg2, "eqtrd");

    // Step 2, the substitute: n sits in the base of the power, so oveq1.
    let subst = seq!(th, add(mul(TWO, NV), ONE), A, TWO, "cexp", p_eqn, "oveq1d");
    let p_tgt = seq!(th, sq, target, asq, calc, subst, "eqtr3d");

    // The first `requires` line of step 6: the witness is an integer.
    let two_zz = seq!(in_zz(TWO), th, "2z a1i");
    let nsq_zz = seq!(th, in_zz(NV), in_zz(&nsq), p_n, NV, "zsqcl syl");
    let w_zz = seq!(
        th,
        mul(TWO, &nsq),
        mul(TWO, NV),
        seq!(th, TWO, nsq, two_zz, nsq_zz, "zmulcld"),
        seq!(th, TWO, NV, two_zz, p_n, "zmulcld"),
        "zaddcld"
    );

    // Step 6, the definition used to conclude an existence claim. The
    // witness is W, read off the cited line, and rspcev wants the claim with
    // m in its place.
    let eqm = eq(add(mul(TWO, MV), ONE), &asq);
    let exm = seq!(eqm, "vm cz wrex");
    let t1 = seq!(MV, w, TWO, "cmul oveq2");
    let t2 = seq!(
        eq(MV, &w),
        mul(TWO, MV),
        mul(TWO, &w),
        ONE,
        "caddc",
        t1,
        "oveq1d"
    );
    let t3 = seq!(
        eq(MV, &w),
        add(mul(TWO, MV), ONE),
        add(mul(TWO, &w), ONE),
        asq,
        t2,
        "eqeq1d"
    );
    let p_exm = seq!(
        th,
        wa(in_zz(&w), eq(&target, &asq)),
        exm,
        seq!(th, in_zz(&w), eq(&target, &asq), w_zz, p_tgt, "jca"),
        eqm,
        eq(&target, &asq),
        "vm",
        w,
        "cz",
        t3,
        "rspcev",
        "syl"
    );

    // and the second `requires`: the thing claimed odd is an integer. Then
    // the definition is read right to left, back to the divisibility form.
    let p_asqzz = seq!(th, in_zz(A), in_zz(&asq), p_azz, A, "zsqcl syl");
    let p_bic = seq!(
        th,
        in_zz(&asq),
        seq!(odd_asq, exm, "wb"),
        p_asqzz,
        "vm",
        asq,
        "odd2np1 syl"
    );
    let inner = seq!(th, odd_asq, exm, p_exm, p_bic, "mpbird");
    let body = seq!(chn, eqn, odd_asq, inner, "ex");

    // and the scope closes: the existential discharges what was proved under
    // it.
    let o_azz = seq!(in_zz(A), odd_a, "simpl");
    let o_odd = seq!(in_zz(A), odd_a, "simpr");
    let o_exn = seq!(
        ch,
        odd_a,
        exn,
        o_odd,
        seq!(
            ch,
            in_zz(A),
            seq!(odd_a, exn, "wb"),
            o_azz,
            "vn",
            A,
            "odd2np1 syl"
        ),
        "mpbid"
    );
    let odd_proof = seq!(
        ch,
        exn,
        odd_asq,
        o_exn,
        seq!(ch, eqn, odd_asq, "vn", "cz", body, "rexlimdva"),
        "mpd"
    );

    // --- even-square --------------------------------------------------------

    // its two hypotheses, and the supposition of step 1
    let ch2 = wa(in_zz(A), dvds(TWO, &asq));
    let ch2s = wa(&ch2, &odd_a);
    let e_azz = seq!(in_zz(A), dvds(TWO, &asq), "simpl");
    let e_ev = seq!(in_zz(A), dvds(TWO, &asq), "simpr");

    // Step 1.1: under the supposition, A squared is odd, by citing
    // odd-square.
    let s_azz = seq!(ch2s, ch2, in_zz(A), seq!(ch2, odd_a, "simpl"), e_azz, "syl");
    let s_odd = seq!(ch2, odd_a, "simpr");
    let e_11 = seq!(
        ch2s,
        ch,
        odd_asq,
        seq!(ch2s, in_zz(A), odd_a, s_azz, s_odd, "jca"),
        A,
        "oddsq",
        "syl"
    );

    // Step 1.2: but the hypothesis says it is even. The contradiction block
    // closes on the two of them, and pm2.65d is what discharges the
    // supposition: there is no separate expansion for the `join` that pairs
    // them.
    let e_12 = seq!(ch2, dvds(TWO, &asq), e_ev, "notnotd");
    let e_1 = seq!(
        ch2,
        odd_a,
        odd_asq,
        seq!(ch2, odd_a, odd_asq, e_11, "ex"),
        seq!(ch2, wn(&odd_asq), odd_a, e_12, "a1d"),
        "pm2.65d"
    );

    // Steps 2 and 3: every integer is even or odd, and this one is not odd.
    let e_or = seq!(wo(dvds(TWO, A), &odd_a), ch2, dvds(TWO, A), "exmid a1i");
    let e_2 = seq!(
        ch2,
        wo(dvds(TWO, A), &odd_a),
        dvds(TWO, A),
        e_or,
        seq!(
            ch2,
            wn(&odd_a),
            wi(wo(dvds(TWO, A), &odd_a), dvds(TWO, A)),
            e_1,
            odd_a,
            dvds(TWO, A),
            "orel2 syl"
        ),
        "mpd"
    );

    format!(
        r#"$( thm:proof/sqrt2-irrational/odd-square and
   thm:proof/sqrt2-irrational/even-square, from proof/sqrt2-irrational.proof,
   as Metamath proofs.

   Verify with any Metamath verifier, with set.mm in the same directory:

       python3 mmverify.py parity.mm

   They were checked against set.mm of 2026-09-19 with mmverify.py, and
   against a copy of that file truncated after oddm1even, which is the last
   statement they use.

   Nothing here is assumed. Every statement is proved from set.mm's own
   theorems, including the two `algebra` steps.
$)

$[ set.mm $]

$( The two `algebra` steps of the readable proof. Each is a normalisation
   with no cited equation, which is what twelve of the corpus's seventeen
   algebra steps are. $)
oalg1 $p |- ( N e. CC -> ( ( ( 2 x. N ) + 1 ) ^ 2 ) =
             ( ( ( 4 x. ( N ^ 2 ) ) + ( 4 x. N ) ) + 1 ) ) $=
  {oalg1} $.

oalg2 $p |- ( N e. CC -> ( ( ( 4 x. ( N ^ 2 ) ) + ( 4 x. N ) ) + 1 ) =
             ( ( 2 x. ( ( 2 x. ( N ^ 2 ) ) + ( 2 x. N ) ) ) + 1 ) ) $=
  {oalg2} $.

${{
  $d n m A $.
  oddsq $p |- ( ( A e. ZZ /\ -. 2 || A ) -> -. 2 || ( A ^ 2 ) ) $=
    {odd_proof} $.
$}}

${{
  evensq $p |- ( ( A e. ZZ /\ 2 || ( A ^ 2 ) ) -> 2 || A ) $=
    {e_2} $.
$}}
"#
    )
}

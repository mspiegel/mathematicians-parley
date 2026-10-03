//! Polynomials, for `proved.mm`.
//!
//! The page says "p is a polynomial" and means one with complex
//! coefficients, set.mm's `Poly ` CC`, a set of functions from ℂ to ℂ. Two
//! items rest on it:
//!
//! - a polynomial's value at a complex number is complex: `plyf` gives the
//!   function's type and `ffvelcdm` its value;
//! - the remainder theorem: p(x) = (x − a)·q(x) + p(a) for every x, with q a
//!   polynomial. set.mm says it of functions (`plyrem`): p less (x − a) times
//!   the quotient `quot` is the constant function p(a). Here that is read at
//!   each x, the operations on functions taken a value at a time (`fnfvof`),
//!   x − a read as the identity less a constant (`idpfv`, `fvconst2g`), and
//!   the quotient is a polynomial because x − a is one of degree 1 and so
//!   not the zero polynomial (`plyremlem`, `dgr0`, `quotcl2`).

use super::parallels::{statement, Prover, Said};
use crate::mm::Builder;
use crate::proofs::Lemma;

pub const HEAD: &str = "$( Polynomials: a value of one, and division by x - a. $)
$( The quotient is the witness of a \"there is\" binding q, and the remainder
   is said of every x; both letters are apart from the polynomial, the point
   and each other. $)
$d q x $.  $d q F $.  $d q A $.  $d x F $.  $d x A $.
";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    let p = Prover { b };
    vec![value(&p), remainder(&p)]
}

fn finish(
    p: &Prover,
    label: &str,
    said: Said,
    conjuncts: &[&str],
    text: &str,
) -> Lemma {
    let said = p.is(p.curried(said, conjuncts), text);
    Lemma::new(label, statement(p, &said), said.proof)
}

/// A polynomial's value at a complex number is complex.
fn value(p: &Prover) -> Lemma {
    let conj = ["F e. ( Poly ` CC )", "A e. CC"];
    let parts = p.parts(&conj);
    let mapping = p.apply("plyf", &[&parts[0]], &[]);
    let said = p.apply("ffvelcdm", &[&mapping, &parts[1]], &[]);
    finish(
        p,
        "gplyval",
        said,
        &conj,
        "( F e. ( Poly ` CC ) -> ( A e. CC -> ( F ` A ) e. CC ) )",
    )
}

/// The remainder theorem: p(x) = (x − a)·q(x) + p(a) for every x ∈ ℂ, with q
/// the quotient of p by x − a.
fn remainder(p: &Prover) -> Lemma {
    let conj = ["F e. ( Poly ` CC )", "A e. CC"];
    let parts = p.parts(&conj);
    let (poly, point) = (&parts[0], &parts[1]);
    let g = Prover::conjoined(&conj);
    let divisor = "( Xp oF - ( CC X. { A } ) )";
    let quotient = format!("( F quot {divisor} )");
    let product = format!("( {divisor} oF x. {quotient} )");
    let rest = format!("( F oF - {product} )");
    let eqid = |class: &str| p.by("eqid", &[], &[("A", class)]);

    // x − a is a polynomial of degree 1, so not the zero polynomial, and
    // the quotient by it is a polynomial.
    let about = p.by(
        "syl",
        &[point, &p.by("plyremlem", &[&eqid(divisor)], &[("A", "A")])],
        &[],
    );
    let divisor_poly = p.by("simp1d", &[&about], &[]);
    let degree_one = p.by("simp2d", &[&about], &[]);
    let not_zero_degree = p.by(
        "eqnetrd",
        &[&degree_one, &p.always(&p.by("ax-1ne0", &[], &[]), &g)],
        &[],
    );
    let zero_degree = p.by(
        "eqtrdi",
        &[
            &p.by("fveq2", &[], &[("A", divisor), ("B", "0p"), ("F", "deg")]),
            &p.by("dgr0", &[], &[]),
        ],
        &[],
    );
    let nonzero = p.by(
        "syl",
        &[&not_zero_degree, &p.by("necon3i", &[&zero_degree], &[])],
        &[],
    );
    let quotient_poly =
        p.apply("quotcl2", &[poly, &divisor_poly, &nonzero], &[("S", "CC")]);

    // set.mm's remainder: p less (x − a) times the quotient is constant.
    let constant = p.by("plyrem", &[&eqid(divisor), &eqid(&rest)], &[("S", "CC")]);

    // At each x.
    let at = "x e. CC";
    let lift = |s: &Said| p.lift(s, at);
    let x_in = p.by("simpr", &[], &[("ph", &g), ("ps", at)]);
    let complex_at = |poly: &Said, arg: &Said| {
        p.apply(
            "ffvelcdm",
            &[&lift(&p.apply("plyf", &[poly], &[])), arg],
            &[],
        )
    };
    let on_cc = |poly: &Said| p.apply("ffn", &[&p.apply("plyf", &[poly], &[])], &[]);
    let value_at_a = p.apply("ffvelcdm", &[&p.apply("plyf", &[poly], &[]), point], &[]);
    let rest_at_x = p.by("fveq1d", &[&lift(&constant)], &[("A", "x")]);
    let constant_at_x = p.apply("fvconst2g", &[&lift(&value_at_a), &x_in], &[]);
    let rest_is_value = p.by("eqtrd", &[&rest_at_x, &constant_at_x], &[]);
    let cc_set = p.always(&p.by("cnex", &[], &[]), &format!("( {g} /\\ {at} )"));
    let where_x = p.by("jca", &[&cc_set, &x_in], &[]);
    let pointwise = |first: &Said, second: &Said, op: &str| {
        let both = p.by("jca", &[first, second], &[]);
        p.apply("fnfvof", &[&both, &where_x], &[("R", op)])
    };
    let product_poly = p.apply("plymulcl", &[&divisor_poly, &quotient_poly], &[]);
    let rest_at = pointwise(&lift(&on_cc(poly)), &lift(&on_cc(&product_poly)), "-");
    let product_at = pointwise(
        &lift(&on_cc(&divisor_poly)),
        &lift(&on_cc(&quotient_poly)),
        "x.",
    );
    let identity = p.always(
        &p.by(
            "mp2an",
            &[
                &p.by("ssid", &[], &[("A", "CC")]),
                &p.by("ax-1cn", &[], &[]),
                &p.by("plyid", &[], &[("S", "CC")]),
            ],
            &[],
        ),
        &g,
    );
    let identity_on = on_cc(&identity);
    let constant_on = p.apply("fnconstg", &[point], &[("A", "CC")]);
    let divisor_at = pointwise(&lift(&identity_on), &lift(&constant_on), "-");
    let x_itself = p.apply("idpfv", &[&x_in], &[]);
    let a_itself = p.apply("fvconst2g", &[&lift(point), &x_in], &[]);
    let divisor_at = p.by(
        "eqtrd",
        &[
            &divisor_at,
            &p.by("oveq12d", &[&x_itself, &a_itself], &[("F", "-")]),
        ],
        &[],
    );
    let quotient_x = format!("( {quotient} ` x )");
    let product_at = p.by(
        "eqtrd",
        &[
            &product_at,
            &p.by("oveq1d", &[&divisor_at], &[("C", &quotient_x), ("F", "x.")]),
        ],
        &[],
    );
    let rest_at = p.by(
        "eqtrd",
        &[
            &rest_at,
            &p.by("oveq2d", &[&product_at], &[("C", "( F ` x )"), ("F", "-")]),
        ],
        &[],
    );
    let difference = p.by("eqtr3d", &[&rest_at, &rest_is_value], &[]);
    let value_x = complex_at(poly, &x_in);
    let quotient_value = complex_at(&quotient_poly, &x_in);
    let shift = p.apply("subcl", &[&x_in, &lift(point)], &[]);
    let times = p.apply("mulcl", &[&shift, &quotient_value], &[]);
    let rule = p.apply("subadd", &[&value_x, &times, &lift(&value_at_a)], &[]);
    let each = p.by("eqcomd", &[&p.by("mpbid", &[&difference, &rule], &[])], &[]);
    let every = p.by("ralrimiva", &[&each], &[]);

    // The quotient is the polynomial there is.
    let swap = p.by("fveq1", &[], &[("F", "q"), ("G", &quotient), ("A", "x")]);
    let swap = p.by("oveq2d", &[&swap], &[("C", "( x - A )"), ("F", "x.")]);
    let swap = p.by("oveq1d", &[&swap], &[("C", "( F ` A )"), ("F", "+")]);
    let swap = p.by("eqeq2d", &[&swap], &[("C", "( F ` x )")]);
    let swap = p.by("ralbidv", &[&swap], &[("x", "x"), ("A", "CC")]);
    let found = p.by("rspcev", &[&swap], &[("B", "( Poly ` CC )")]);
    let said = p.by("syl2anc", &[&quotient_poly, &every, &found], &[]);
    finish(
        p,
        "gplyrem",
        said,
        &conj,
        "( F e. ( Poly ` CC ) -> ( A e. CC -> E. q e. ( Poly ` CC ) A. x e. CC ( F ` x ) = ( ( ( x - A ) x. ( q ` x ) ) + ( F ` A ) ) ) )",
    )
}

//! Divisor sums, for `proved.mm`.
//!
//! set.mm's sigma takes a power first: A sigma n is the sum of the A-th
//! powers of the divisors of n. The page writes σ(n), the sum of the
//! divisors themselves, which is 1 sigma n, and set.mm states its value only
//! with the power left in. So each lemma here is set.mm's with the power 1
//! written away:
//!
//! - σ(n) is the sum of the divisors of n: `sgmval2` at 1, with each k^1
//!   read as k by `exp1`, for `def:stdlib/divisibility/σ`;
//! - σ of a prime's power is the sum of the powers up to it: `sgmppw` at 1,
//!   with p^c 1 read as p by `cxp1`, for
//!   `thm:stdlib/divisibility/sigma-prime-power`.

use crate::binds;
use crate::mm::Builder;
use crate::proofs::Lemma;

pub const HEAD: &str =
    "$( Divisors: the sum of the divisors of a number, and of a prime's powers. $)
$d k p B $.
$d k N $.
$d k P $.

";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![sum_of_divisors(b), prime_power(b)]
}

/// ( B e. NN -> ( 1 sigma B ) = sum_ k e. { p e. NN | p || B } k )
fn sum_of_divisors(b: &Builder) -> Lemma {
    let v = |var: &str| b.float(var);
    let set = "{ p e. NN | p || B }";
    let natural = b.wff("B e. NN");
    let member = b.wff(&format!("k e. {set}"));
    let with_power = format!("sum_ k e. {set} ( k ^ 1 )");
    let without = format!("sum_ k e. {set} k");

    // sgmval2 at 1, which is an integer.
    let value = b.ap(
        "mpan",
        &binds! {"ph" => b.wff("1 e. ZZ"), "ps" => natural.clone(),
        "ch" => b.wff(&format!("( 1 sigma B ) = {with_power}"))},
        &[
            &b.step("1z"),
            &b.ap(
                "sgmval2",
                &binds! {"A" => b.class("1"), "B" => b.class("B"), "k" => v("k"), "p" => v("p")},
                &[],
            ),
        ],
    );

    // Each divisor is a natural number, so a complex one, and its first
    // power is itself.
    let at_k = b.wff(&format!("( B e. NN /\\ k e. {set} )"));
    let in_set = b.ap(
        "simpr",
        &binds! {"ph" => natural.clone(), "ps" => member.clone()},
        &[],
    );
    let in_nn = b.ap(
        "syl",
        &binds! {"ph" => at_k.clone(), "ps" => member.clone(), "ch" => b.wff("k e. NN")},
        &[
            &in_set,
            &b.ap(
                "elrabi",
                &binds! {"A" => b.class("k"), "x" => v("p"), "V" => b.class("NN"),
                "ph" => b.wff("p || B")},
                &[],
            ),
        ],
    );
    let in_cc = b.ap(
        "syl",
        &binds! {"ph" => at_k.clone(), "ps" => b.wff("k e. NN"), "ch" => b.wff("k e. CC")},
        &[&in_nn, &b.ap("nncn", &binds! {"A" => b.class("k")}, &[])],
    );
    let first_power = b.ap(
        "syl",
        &binds! {"ph" => at_k, "ps" => b.wff("k e. CC"), "ch" => b.wff("( k ^ 1 ) = k")},
        &[&in_cc, &b.ap("exp1", &binds! {"A" => b.class("k")}, &[])],
    );
    let sums = b.ap(
        "sumeq2dv",
        &binds! {"ph" => natural.clone(), "k" => v("k"), "A" => b.class(set),
        "B" => b.class("( k ^ 1 )"), "C" => b.class("k")},
        &[&first_power],
    );

    Lemma::new(
        "g1sgmval",
        format!("|- ( B e. NN -> ( 1 sigma B ) = {without} )"),
        b.ap(
            "eqtrd",
            &binds! {"ph" => natural, "A" => b.class("( 1 sigma B )"),
            "B" => b.class(&with_power), "C" => b.class(&without)},
            &[&value, &sums],
        ),
    )
}

/// ( ( P e. Prime /\ N e. NN0 ) ->
///   ( 1 sigma ( P ^ N ) ) = sum_ k e. ( 0 ... N ) ( P ^ k ) )
fn prime_power(b: &Builder) -> Lemma {
    let v = |var: &str| b.float(var);
    let range = "( 0 ... N )";
    let ph = b.wff("( P e. Prime /\\ N e. NN0 )");
    let with_power = format!("sum_ k e. {range} ( ( P ^c 1 ) ^ k )");
    let without = format!("sum_ k e. {range} ( P ^ k )");

    // sgmppw at 1, which is a complex number.
    let value = b.ap(
        "mp3an1",
        &binds! {"ph" => b.wff("1 e. CC"), "ps" => b.wff("P e. Prime"),
        "ch" => b.wff("N e. NN0"),
        "th" => b.wff(&format!("( 1 sigma ( P ^ N ) ) = {with_power}"))},
        &[
            &b.step("ax-1cn"),
            &b.ap(
                "sgmppw",
                &binds! {"A" => b.class("1"), "P" => b.class("P"), "N" => b.class("N"),
                "k" => v("k")},
                &[],
            ),
        ],
    );

    // The prime is a complex number, so its first complex power is itself.
    let prime = b.ap(
        "simpl",
        &binds! {"ph" => b.wff("P e. Prime"), "ps" => b.wff("N e. NN0")},
        &[],
    );
    let natural = b.ap(
        "syl",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("P e. Prime"), "ch" => b.wff("P e. NN")},
        &[&prime, &b.ap("prmnn", &binds! {"P" => b.class("P")}, &[])],
    );
    let complex = b.ap(
        "syl",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("P e. NN"), "ch" => b.wff("P e. CC")},
        &[&natural, &b.ap("nncn", &binds! {"A" => b.class("P")}, &[])],
    );
    let first_power = b.ap(
        "syl",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("P e. CC"),
        "ch" => b.wff("( P ^c 1 ) = P")},
        &[&complex, &b.ap("cxp1", &binds! {"A" => b.class("P")}, &[])],
    );
    let term = b.ap(
        "oveq1d",
        &binds! {"ph" => ph.clone(), "A" => b.class("( P ^c 1 )"), "B" => b.class("P"),
        "C" => b.class("k"), "F" => b.class("^")},
        &[&first_power],
    );
    let at_k = b.ap(
        "adantr",
        &binds! {"ph" => ph.clone(), "ps" => b.wff("( ( P ^c 1 ) ^ k ) = ( P ^ k )"),
        "ch" => b.wff(&format!("k e. {range}"))},
        &[&term],
    );
    let sums = b.ap(
        "sumeq2dv",
        &binds! {"ph" => ph.clone(), "k" => v("k"), "A" => b.class(range),
        "B" => b.class("( ( P ^c 1 ) ^ k )"), "C" => b.class("( P ^ k )")},
        &[&at_k],
    );

    Lemma::new(
        "g1sgmppw",
        format!(
            "|- ( ( P e. Prime /\\ N e. NN0 ) -> ( 1 sigma ( P ^ N ) ) = {without} )"
        ),
        b.ap(
            "eqtrd",
            &binds! {"ph" => ph, "A" => b.class("( 1 sigma ( P ^ N ) )"),
            "B" => b.class(&with_power), "C" => b.class(&without)},
            &[&value, &sums],
        ),
    )
}

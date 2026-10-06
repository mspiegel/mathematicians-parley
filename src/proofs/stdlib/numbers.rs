//! Numbers, for `proved.mm`.
//!
//! What the proofs ask of whole numbers that set.mm says only of a wider
//! system, each reached by `zre` and `nnrp`: a remainder on dividing an
//! integer by a natural number is less than the divisor (`modlt`, for
//! `mun:stdlib/divisibility/mod-less`), and adding a multiple of the divisor
//! leaves the remainder as it was (`muladdmod`, for
//! `mun:stdlib/divisibility/mod-multiple`).

use crate::binds;
use crate::mm::Builder;
use crate::proofs::Lemma;

pub const HEAD: &str = "$( Numbers: a remainder is less than its divisor, and a multiple of\n   the divisor added leaves it as it was. $)\n\n";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![mod_less(b), mod_multiple(b)]
}

/// ( ( A e. ZZ /\ M e. NN /\ N e. ZZ ) -> ( ( ( N x. M ) + A ) mod M ) = ( A mod M ) )
fn mod_multiple(b: &Builder) -> Lemma {
    Lemma::new(
        "gmuladdmod",
        "|- ( ( A e. ZZ /\\ M e. NN /\\ N e. ZZ ) -> ( ( ( N x. M ) + A ) mod M ) = ( A mod M ) )",
        b.ap(
            "syl3an",
            &binds! {"ph" => b.wff("A e. ZZ"), "ps" => b.wff("A e. RR"),
            "ch" => b.wff("M e. NN"), "th" => b.wff("M e. RR+"),
            "ta" => b.wff("N e. ZZ"), "et" => b.wff("N e. ZZ"),
            "ze" => b.wff("( ( ( N x. M ) + A ) mod M ) = ( A mod M )")},
            &[
                &b.ap("zre", &binds! {"N" => b.class("A")}, &[]),
                &b.ap("nnrp", &binds! {"A" => b.class("M")}, &[]),
                &b.ap("id", &binds! {"ph" => b.wff("N e. ZZ")}, &[]),
                &b.ap(
                    "muladdmod",
                    &binds! {"A" => b.class("A"), "M" => b.class("M"), "N" => b.class("N")},
                    &[],
                ),
            ],
        ),
    )
}

/// ( ( A e. ZZ /\ B e. NN ) -> ( A mod B ) < B )
fn mod_less(b: &Builder) -> Lemma {
    Lemma::new(
        "gzmodlt",
        "|- ( ( A e. ZZ /\\ B e. NN ) -> ( A mod B ) < B )",
        b.ap(
            "syl2an",
            &binds! {"ph" => b.wff("A e. ZZ"), "ps" => b.wff("A e. RR"),
            "ta" => b.wff("B e. NN"), "ch" => b.wff("B e. RR+"),
            "th" => b.wff("( A mod B ) < B")},
            &[
                &b.ap("zre", &binds! {"N" => b.class("A")}, &[]),
                &b.ap("nnrp", &binds! {"A" => b.class("B")}, &[]),
                &b.ap(
                    "modlt",
                    &binds! {"A" => b.class("A"), "B" => b.class("B")},
                    &[],
                ),
            ],
        ),
    )
}

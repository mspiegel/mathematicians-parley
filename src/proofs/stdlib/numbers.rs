//! Numbers, for `proved.mm`.
//!
//! What Euclid's algorithm asks of whole numbers that set.mm says only of a
//! wider system: a remainder on dividing an integer by a natural number is
//! less than the divisor. `modlt` says it of a real and a positive real, and
//! `zre` and `nnrp` reach those, for `mun:stdlib/divisibility/mod-less`.

use crate::binds;
use crate::mm::Builder;
use crate::proofs::Lemma;

pub const HEAD: &str = "$( Numbers: a remainder is less than its divisor. $)\n\n";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    vec![mod_less(b)]
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

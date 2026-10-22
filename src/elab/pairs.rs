//! Two pairs compared coordinate by coordinate, proved (`METHODS.md`,
//! Pairs). The method a step names proves the coordinates' equations, or
//! one coordinate's difference, as it proves any of its own; what is here
//! carries that to the pairs. What decides it is `crate::methods::pairs`.

use super::state::Elaborator;
use super::Facts;
use crate::binds;
use crate::methods::pairs::{Coordinate, PairRelation};
use crate::mm::spell::Proof;
use crate::mm::Rpn;
use crate::outcome::Checked;
use crate::t;

/// ( scope -> x ∈ class ) for one of the left pair's coordinates: what
/// `opthg` asks of each before it reads two pairs by their parts.
pub struct InClass {
    pub proof: Proof,
    pub class: Rpn,
}

impl<'a> Elaborator<'a> {
    /// The left pair's coordinates as numbers, ( scope -> x ∈ ℂ ) each:
    /// what `pairs_apart` asks of a pair of numbers.
    pub fn number_members(
        &mut self,
        pairs: &PairRelation,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<[InClass; 2]> {
        let mut out = Vec::new();
        for x in &pairs.left {
            let said = self.rpn(x);
            out.push(InClass {
                proof: self.membership(&said, "cc", scope, facts)?,
                class: t!("cc"),
            });
        }
        let [first, second]: [InClass; 2] =
            out.try_into().ok().expect("two coordinates");
        Ok([first, second])
    }

    /// ( scope -> <. a , b >. = <. c , d >. ), from ( scope -> a = c ) and
    /// ( scope -> b = d ) (`opeq12d`).
    pub fn pairs_equal(
        &mut self,
        pairs: &PairRelation,
        scope: &Rpn,
        first: &Proof,
        second: &Proof,
    ) -> Proof {
        let [a, b] = [&pairs.left[0], &pairs.left[1]].map(|t| self.rpn(t));
        let [c, d] = [&pairs.right[0], &pairs.right[1]].map(|t| self.rpn(t));
        self.b.ap(
            "opeq12d",
            &binds! {"ph" => scope, "A" => &a, "B" => &c, "C" => &b, "D" => &d},
            &[first, second],
        )
    }

    /// ( scope -> the pairs differ ), as the claim spells it, from
    /// ( scope -> ¬ x = y ) at the coordinate `at`: two pairs are one just
    /// where both coordinates are (`opthg`), and one pair of coordinates
    /// is not.
    pub fn pairs_apart(
        &mut self,
        pairs: &PairRelation,
        scope: &Rpn,
        at: Coordinate,
        apart: &Proof,
        members: &[InClass; 2],
    ) -> Proof {
        let [a, b] = [&pairs.left[0], &pairs.left[1]].map(|t| self.rpn(t));
        let [c, d] = [&pairs.right[0], &pairs.right[1]].map(|t| self.rpn(t));
        let (one, other) = (t!(&a, &b, "cop"), t!(&c, &d, "cop"));
        let same = t!(&one, &other, "wceq");
        let (first, second) = (t!(&a, &c, "wceq"), t!(&b, &d, "wceq"));
        let both = t!(&first, &second, "wa");
        let (in_v, in_w) = (
            t!(&a, &members[0].class, "wcel"),
            t!(&b, &members[1].class, "wcel"),
        );
        let held = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => &in_v, "ch" => &in_w},
            &[&members[0].proof, &members[1].proof],
        );
        let law = self.b.ap(
            "opthg",
            &binds! {"A" => &a, "B" => &b, "C" => &c, "D" => &d,
            "V" => &members[0].class, "W" => &members[1].class},
            &[],
        );
        let parts = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => &t!(&in_v, &in_w, "wa"),
            "ch" => &t!(&same, &both, "wb")},
            &[&held, &law],
        );
        let neither = match at {
            Coordinate::First => self.b.ap(
                "intnanrd",
                &binds! {"ph" => scope, "ps" => &first, "ch" => &second},
                &[apart],
            ),
            Coordinate::Second => self.b.ap(
                "intnand",
                &binds! {"ph" => scope, "ps" => &second, "ch" => &first},
                &[apart],
            ),
        };
        let denied = self.b.ap(
            "mtbird",
            &binds! {"ph" => scope, "ps" => &same, "ch" => &both},
            &[&neither, &parts],
        );
        if !pairs.spelt_ne {
            return denied;
        }
        let spelt = self
            .b
            .ap("df-ne", &binds! {"A" => &one, "B" => &other}, &[]);
        self.b.ap(
            "sylibr",
            &binds! {"ph" => scope, "ps" => &t!(&same, "wn"),
            "ch" => &t!(&one, &other, "wne")},
            &[&denied, &spelt],
        )
    }
}

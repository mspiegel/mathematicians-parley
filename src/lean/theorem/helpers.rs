//! What an obtain takes, widening and the proof's small helpers.

use super::*;

/// What an `obtain` takes its witnesses from: the Lean term that proves the
/// "there is", and the "there is" itself.
pub(super) struct Obtained {
    pub(super) term: Printed,
    pub(super) says: Node,
    /// What the cited item's letters stand for, the Y of "there is s ∈ Y"
    /// given ℕ; empty for a line of the proof, which writes its own sets.
    pub(super) binding: crate::matching::Binding,
    /// The "there is" as Lean states it at the item's values, which the
    /// `obtain` takes apart; None of a line of the proof, which the writer
    /// states itself.
    pub(super) lean: Option<Printed>,
}

/// A cited line as a step uses it: the name to use, and the `have` that
/// casts it up to the claim's type where it is narrower.
pub(super) struct Widened {
    pub(super) have: Option<Tactic>,
    /// The line as the claim's type has it: the line itself, or the name
    /// of its widened copy.
    pub(super) name: Printed,
}

/// `congrArg (fun x : A => (x : B)) e`: the equation e of A mapped into B.
pub(super) fn cast_up(
    writer: &Writer,
    own: super::super::templates::Num,
    wanted: super::super::templates::Num,
    equation: Printed,
) -> Printed {
    let x = Printed::cast(super::super::tactics::hyp("x"), writer.num_type(wanted));
    Printed::applied(
        "congrArg",
        super::super::doc::Source::Core,
        vec![lambda("x", writer.num_type(own), x), equation],
        super::super::doc::LeanType::Prop,
    )
}

/// How a statement Lean derives meets the claim (`Proof::powers_met`).
pub(super) enum PowersMet {
    /// Apart only in powers, converted by this proof.
    Converted(Box<super::super::doc::Proof>),
    /// Alike in every form the writer chose.
    Alike,
    /// Apart otherwise.
    Apart,
}

/// How Lean writes `node` where a natural number is wanted
/// (`Writer::natural_form`), an integer the step's lines show at least 0,
/// p − 1 of the requires line p − 1 ∈ ℕ₀, or name as a whole number by its
/// `toNat` (`Writer::named_whole`), written as its `toNat`.
pub(super) fn natural_form_named(
    writer: &Writer,
    node: &Node,
) -> super::super::expr::NaturalForm {
    use super::super::expr::NaturalForm;
    match writer.natural_form(node) {
        NaturalForm::Integer
            if writer.named_whole(node) || writer.nonnegative(node) =>
        {
            NaturalForm::ToNat
        }
        form => form,
    }
}

/// Whether a statement as Lean writes it holds a cast.
pub(super) fn holds_cast(p: &Printed) -> bool {
    p.walk()
        .iter()
        .any(|c| matches!(c.kind, super::super::doc::TermKind::Cast { .. }))
}

/// Whether a statement as Lean writes it names no letter: numerals and
/// functions of them alone, which `norm_num` works out whole.
pub(super) fn no_letter(t: &Printed) -> bool {
    !t.walk()
        .iter()
        .any(|n| matches!(n.kind, super::super::doc::TermKind::Letter(_)))
}

/// Whether the place at `path` in `start` is a power's exponent, the second
/// child of a `POWER`.
pub(super) fn place_is_exponent(start: &Node, path: &[usize]) -> bool {
    let Some((&last, up)) = path.split_last() else {
        return false;
    };
    last == 1
        && at_path(start, up).is_some_and(|n| n.notation() == crate::notations::POWER)
}

/// Whether a line as the page writes it applies a function to numerals
/// worked on, F(0 + 1) or F(1 + 1), which Lean reads as another atom than
/// F(1) or F(2) until the numerals are worked out.
pub(super) fn numerals_in_an_argument(node: &Node) -> bool {
    node.walk().iter().any(|n| {
        n.notation() == crate::notations::APPLICATION
            && n.children.iter().skip(1).any(|a| {
                !a.children.is_empty() && !a.walk().iter().any(|p| p.is_name())
            })
    })
}

/// Whether a statement as Lean writes it casts a term that is no letter or
/// numeral, `(Real.cos 0 : ℂ)`, which `push_cast` moves into it.
pub(super) fn casts_compound(p: &Printed) -> bool {
    use super::super::doc::TermKind;
    p.walk().iter().any(|c| match &c.kind {
        TermKind::Cast { inner, .. } => !matches!(
            bare_term(inner).kind,
            TermKind::Letter(_) | TermKind::Numeral(_)
        ),
        _ => false,
    })
}

/// `have name : says := by have h := ↑proof; push_cast at h; linear_combination
/// h`: an equation proved in `from` stated in the wider `to`, cast up and its
/// casts pushed in, in the statement too where it casts a compound term
/// (`casts_compound`). `norm_cast` does not take a sum of rationals to the
/// reals, which this does.
pub(super) fn widening_have(
    writer: &Writer,
    name: &str,
    says: Printed,
    from: super::super::templates::Num,
    to: super::super::templates::Num,
    proof: Printed,
) -> Tactic {
    use super::super::tactics as t;
    let goal = casts_compound(&says);
    Tactic::Have {
        name: name.to_string(),
        says,
        proof: Box::new(super::super::doc::Proof::By(Tactic::Seq(vec![
            t::name_h(&cast_up(writer, from, to, proof)),
            t::push_cast(Some(t::at_h(goal))),
            t::linear_combination(t::hyp("h")),
        ]))),
    }
}

/// The tactic that works out a claim of numerals alone (`arithmetic`), by
/// what its Lean statement holds: a sum or product over a range of
/// numerals, `decide`, which works it out term by term, or, where it
/// divides, `field_simp; norm_cast`, which clears the division and works
/// out the integers; a factorial, `norm_num [Nat.factorial]`, which
/// unfolds it; a fraction denied to be a whole number, `1/76 ∉ ℕ`, the
/// whole number taken and its equation cleared to integers, which `omega`
/// refutes; anything else `norm_num`. A binomial coefficient declines:
/// `norm_num` does not work one out.
pub(super) fn worked_out(says: &Printed) -> Route<Tactic> {
    use super::super::doc::{BoundForm, Brackets, Op, TermKind};
    use super::super::tactics as t;
    let parts = says.walk();
    let applied = |name: &str| {
        parts.iter().any(
            |p| matches!(&p.kind, TermKind::App { head, .. } if head.text() == name),
        )
    };
    if applied("LeanBridges.Counting.choose") {
        return Route::no(
            "a binomial coefficient of numerals, which norm_num does not work out",
        );
    }
    if let Some(taken) = whole_number_denied(says) {
        let name = |n: &str| Printed::letter(n, super::super::doc::LeanType::Prop);
        let mut pattern = vec![name(&taken.letter)];
        if taken.bounded {
            pattern.push(name("_"));
        }
        pattern.push(name("h"));
        let listed = Printed {
            kind: TermKind::Listed {
                brackets: Brackets::Angle,
                items: pattern,
            },
            ty: None,
        };
        let at_h =
            || TacticArg::At(vec![super::super::doc::Location::Hypothesis("h".into())]);
        return Route::Built(Tactic::Seq(vec![
            t::call("rintro", vec![TacticArg::Term(listed)]),
            t::call("field_simp", vec![at_h()]),
            t::call("norm_cast", vec![at_h()]),
            t::call("omega", vec![]),
        ]));
    }
    let ranged = parts.iter().any(|p| {
        matches!(
            &p.kind,
            TermKind::Bound {
                form: BoundForm::BigOp { .. },
                ..
            }
        )
    });
    let divides = parts
        .iter()
        .any(|p| matches!(&p.kind, TermKind::Infix { op, .. } if *op == Op::DIVIDE));
    Route::Built(match (ranged, divides) {
        (true, true) => Tactic::Seq(vec![
            t::call("field_simp", vec![]),
            t::call("norm_cast", vec![]),
        ]),
        (true, false) => t::call("decide", vec![]),
        (false, _) if applied("LeanBridges.Counting.factorial") => {
            t::call("norm_num", vec![t::rules(vec![t::lemma("Nat.factorial")])])
        }
        (false, _) => t::call("norm_num", vec![]),
    })
}

/// The whole number a claim `¬ (∃ m : ℤ, 0 < m ∧ (m : ℚ) = x)` denies `x`
/// is, as Lean writes `x ∉ ℕ`.
pub(super) struct WholeNumberDenied {
    pub(super) letter: String,
    /// Whether the whole number has a bound beside its equation, `0 < m ∧`,
    /// as of ℕ and ℕ₀, and not of ℤ.
    pub(super) bounded: bool,
}

pub(super) fn whole_number_denied(says: &Printed) -> Option<WholeNumberDenied> {
    use super::super::doc::{Op, Quant, TermKind};
    let bare = |t: &Printed| -> Printed {
        let mut t = t.clone();
        while let TermKind::Paren(inner) = t.kind {
            t = *inner;
        }
        t
    };
    let TermKind::Not(inner) = &bare(says).kind else {
        return None;
    };
    let TermKind::Quantified {
        quant: Quant::Exists,
        letter,
        guard,
        body,
        ..
    } = bare(inner).kind
    else {
        return None;
    };
    let bounded = guard.is_some()
        || matches!(&bare(&body).kind, TermKind::Infix { op, .. } if *op == Op::AND);
    Some(WholeNumberDenied { letter, bounded })
}

/// What a cited item and its claim are compared as (`Proof::agreement`).
pub(super) struct AgreementAsked<'a> {
    /// What differs between the two once counts and powers are read alike.
    pub(super) found: Vec<super::super::doc::forms::FormDifference>,
    /// What the reading gives, as Lean states it at the citation's values.
    pub(super) compared: &'a Printed,
    /// The claim as Lean states it.
    pub(super) claim: &'a Printed,
    /// The claim with the identity elements dropped.
    pub(super) claim_read: &'a Printed,
    /// Whether the item's equation faces the claim the other way.
    pub(super) turned: bool,
    /// The sets whose counts differ only in form.
    pub(super) counted: &'a [Printed],
    /// The exponents whose powers differ only in form.
    pub(super) powered: &'a [NonNegative],
    /// Whether an integer power of a natural number cast up is converted.
    pub(super) cast_powers: bool,
    /// The powers under a sum whose exponent names its letter.
    pub(super) bound: &'a [super::super::doc::forms::BoundPower],
    /// The identity elements the checker dropped meeting the two.
    pub(super) identities: Vec<&'static str>,
    /// The page line of the step.
    pub(super) line: usize,
    /// The item cited.
    pub(super) item: &'a str,
}

/// How a cited item agrees with its claim (`Proof::agreement`).
pub(super) struct Agreement {
    /// Whether `exact` alone closes the line.
    pub(super) agrees: bool,
    /// Whether the identity elements dropped are all that stands apart.
    pub(super) by_identities: bool,
    /// The identity rewrites, with the casts of the units added where they
    /// are all that stands apart.
    pub(super) identities: Vec<&'static str>,
}

/// What a citation's closing is asked for (`Proof::close_citation`).
pub(super) struct CitationClosing<'c> {
    /// The claim.
    pub(super) node: &'c Node,
    /// The claim's sentence the citation proves.
    pub(super) k: usize,
    /// What the checker met the citation with.
    pub(super) cited: &'c crate::checker::record::Cited,
    /// The item's sentence.
    pub(super) sentence: &'c Sentence,
    /// Which way the sentence is read.
    pub(super) way: Way,
    /// The path to the part of the "and" the claim is, where it is one.
    pub(super) path: Option<Vec<&'static str>>,
    /// The claim as Lean states it.
    pub(super) claim_lean: Option<Printed>,
    /// Whether a line states the claim as Lean does (`stated_form`).
    pub(super) stated: bool,
}

/// Which part of a cited item's sentence a claim is
/// (`Proof::projected_reading`).
pub(super) struct Projection<'p> {
    /// The claim.
    pub(super) node: &'p Node,
    /// Whether the item's sentence is a biconditional.
    pub(super) iff: bool,
    /// The item's sentence.
    pub(super) sentence: &'p Sentence,
    /// The part of the "and" the reading gives that the checker met the
    /// claim with.
    pub(super) part: Option<usize>,
    /// What the checker met the citation with.
    pub(super) cited: &'p crate::checker::record::Cited,
    /// The claim's sentence the citation proves.
    pub(super) k: usize,
}

/// A citation's term taken to the part of the item's sentence the claim is
/// (`Proof::projected_reading`).
pub(super) struct ProjectedReading {
    /// The term, projected.
    pub(super) term: Printed,
    /// What the term says, as Lean has it.
    pub(super) says: Option<Printed>,
    /// The path to the part of the "and", where the claim is one.
    pub(super) path: Option<Vec<&'static str>>,
}

/// What a cited item and its claim differ in as integer and natural powers
/// (`Proof::compare_powers`).
pub(super) struct PowerForms {
    /// What still differs once the powers are read alike.
    pub(super) found: Vec<super::super::doc::forms::FormDifference>,
    /// The exponents whose powers differ only in form, each with why it is
    /// at least 0.
    pub(super) powered: Vec<NonNegative>,
    /// Whether an integer power of a natural number cast up is converted to
    /// the natural power alike.
    pub(super) cast_powers: bool,
    /// The powers under a sum whose exponent names its letter.
    pub(super) bound: Vec<super::super::doc::forms::BoundPower>,
}

/// What a definition's sentence read backwards is asked for
/// (`Proof::definition_backwards`).
pub(super) struct Backwards<'b> {
    /// The step's reason, which names the lines the witness is found in.
    pub(super) reason: Reason<'b>,
    /// The claim's sentence the citation proves.
    pub(super) k: usize,
    /// The claim.
    pub(super) node: &'b Node,
    /// What the checker met the citation with.
    pub(super) cited: &'b crate::checker::record::Cited,
    /// The item's sentence the definition is read from.
    pub(super) sentence: &'b Sentence,
    /// What the item's sentence says at the citation's values.
    pub(super) statement: &'b Printed,
    /// The item applied to what the citation gives it.
    pub(super) inst: Printed,
    /// The claim as Lean states it.
    pub(super) claim_lean: &'b Option<Printed>,
    /// Whether a line states the claim as Lean does (`stated_form`).
    pub(super) stated: bool,
}

/// How a cited item says what the claim says (`Proof::compare_forms`): the
/// ways the two write one term in different forms, which a citation's proof
/// converts.
pub(super) struct FormComparison {
    /// The sets whose counts differ only in form, to be converted.
    pub(super) counted: Vec<Printed>,
    /// The sets the two count, each with why it is finite.
    pub(super) finite: Vec<ShownFinite>,
    /// The exponents whose powers differ only in form, each with why it is at
    /// least 0, converted alike.
    pub(super) powered: Vec<NonNegative>,
    /// Whether an integer power of a natural number cast up is converted to
    /// the natural power alike.
    pub(super) cast_powers: bool,
    /// The powers under a sum whose exponent names its letter, converted for
    /// each letter in its range.
    pub(super) bound: Vec<super::super::doc::forms::BoundPower>,
    /// The rewrites of the identity elements the checker dropped meeting the
    /// reading with the claim (`Cited::meetings`).
    pub(super) identities: Vec<&'static str>,
    /// Whether a numeral's `toNat` is left once a reading is worked out.
    pub(super) numeral_to_nat: bool,
    /// Whether the line is the item's equation turned round, compared turned
    /// back and closed by the equation's `symm`.
    pub(super) turned: bool,
    /// Whether the item's statement, its letters given, is the line as Lean
    /// writes it, up to what Lean takes as one term, so that `exact` alone
    /// closes the line. Two that are alike but for casts are not enough: an
    /// item over any ring given ℤ writes `n ^ (2 : ℤ)`, which ℤ has no power
    /// for, and the comparison keeps casts.
    pub(super) agrees: bool,
    /// Whether the item is the line once the identity elements the checker
    /// dropped are dropped from both, with nothing else apart: closed by
    /// those rewrites, as a conversion of them alone.
    pub(super) by_identities: bool,
}

/// What a citation gives a cited item (`Proof::instance_of`).
#[derive(Clone, Copy)]
pub(super) struct InstanceAsked<'c> {
    /// The item's sentence.
    pub(super) sentence: &'c Sentence,
    /// What the citation gives each of the item's letters.
    pub(super) binding: &'c crate::matching::Binding,
    /// The step's claim, where it has one.
    pub(super) claim: Option<&'c Node>,
    /// The types the item's things are taken at.
    pub(super) things: &'c ThingsGiven,
    /// The type the item's general letters take.
    pub(super) general: Option<super::super::templates::Num>,
}

/// A calculation's terms as Lean writes them (`chain_printed`).
pub(super) struct ChainPrinted {
    /// Each term, in the type the chain is worked in.
    pub(super) printed: Vec<Printed>,
    /// The type the chain is worked in; ℤ for a chain of sets or of counts,
    /// which have no number type to work in.
    pub(super) at: super::super::templates::Num,
    /// Whether the chain is of sets or of their members.
    pub(super) of_sets: bool,
    /// Whether the chain is of counts.
    pub(super) of_counts: bool,
}

/// Each term of a calculation as Lean writes it. A chain of sets or of
/// their members, A ∩ B = B ∩ A = ∅ or F(F⁻¹(C)) = F(x), is written as sets
/// are; a chain of counts, |A| = |∅| = 0, is in ℕ∞ (`sets::count_term`);
/// any other is worked in the least number type that holds every term,
/// from ℤ, as the claim it proves is written.
pub(super) fn chain_printed(writer: &Writer, terms: &[Node]) -> Route<ChainPrinted> {
    let of_sets = terms
        .iter()
        .any(|t| writer.members_of(t).is_some() || writer.member_kind(t).is_some());
    let of_counts = terms.iter().any(|t| writer.counts(t));
    let mut at = super::super::templates::Num::Int;
    let mut printed = Vec::new();
    if of_counts {
        for t in terms {
            match writer.count_term(t) {
                Route::Built(p) => printed.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
    } else if of_sets {
        for t in terms {
            match writer.set_term(t) {
                Route::Built(p) => printed.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
    } else {
        for t in terms {
            match writer.carrier(t) {
                Route::Built(n) => at = at.max(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        for t in terms {
            match writer.number(t, at) {
                Route::Built(p) => printed.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // A first term whose type nothing in it fixes, numerals alone or
        // a power whose letters are only in its exponent, is told its
        // type, bracketed inside as it stands in the chain.
        if !writer.pinned(&terms[0]) {
            let first = printed[0].clone();
            let first = match first.prec() < 51 {
                true => super::super::tactics::bracket(first),
                false => first,
            };
            printed[0] = Printed::cast(first, writer.num_type(at));
        }
    }
    Route::Built(ChainPrinted {
        printed,
        at,
        of_sets,
        of_counts,
    })
}

/// One row of a calculation, with the chain it is a row of
/// (`Proof::calculation`).
#[derive(Clone, Copy)]
pub(super) struct CalcRow<'c> {
    /// The row's place in the chain: its terms are `terms[index]` and
    /// `terms[index + 1]`.
    pub(super) index: usize,
    /// The chain line the row is.
    pub(super) line: &'c crate::corpus::proof::ChainLine,
    /// The relation the row joins its terms by.
    pub(super) relation: &'c str,
    /// The modulus of a congruence, as Lean writes it.
    pub(super) modulus: &'c Option<Printed>,
    /// The chain's terms, as the page writes them.
    pub(super) terms: &'c [Node],
    /// The chain's terms, as Lean writes them.
    pub(super) printed: &'c [Printed],
}

/// How the places of a recorded putting are written
/// (`Proof::put_exponents`).
pub(super) struct PutExponents {
    /// Whether a side holds a cast of a `toNat`.
    pub(super) cast_to_nat: bool,
    /// Whether the equation is put in ℕ, at exponents or at the count of a
    /// finite set.
    pub(super) natural_exponent: bool,
    /// Whether the term put is a natural number written as it stands, and
    /// not a numeral.
    pub(super) natural_put: bool,
    /// Whether the motive's letter is said whole, as the exponents are.
    pub(super) whole_was: bool,
    /// Whether the exponents are integers, converted to the claim's natural
    /// powers after.
    pub(super) int_exponent: bool,
}

/// The equation a recorded putting uses (`Proof::putting_equation`).
pub(super) struct PuttingEquation {
    /// The line's part the equation is taken from, or the row's change.
    pub(super) part: super::super::algebra::Cited,
    /// The part's proof, facing as the putting uses it.
    pub(super) equation: Printed,
}

/// A recorded substitution read for writing: the equation put at the places
/// of a line or of a claim side, with the motive's letter and the types the
/// places are written in (`Proof::substituted_as_written`).
pub(super) struct Putting<'r, 'w> {
    /// The checker's record of the substitution.
    pub(super) rec: &'r crate::checker::record::Substituted,
    /// The row whose change is the equation, where the step is a row.
    pub(super) row: Option<&'r GivenEquation>,
    /// The page line of the step.
    pub(super) line: usize,
    /// The step's claim.
    pub(super) claim: &'r Node,
    /// The term the equation puts for.
    pub(super) was: &'r Node,
    /// The term the equation puts.
    pub(super) now: &'r Node,
    /// The type the equation is written in.
    pub(super) ty: super::super::templates::Num,
    /// The equation's proof, in `ty` or, where `haves` states it so, in ℕ.
    pub(super) equation: Printed,
    /// What every way out states before its proof.
    pub(super) haves: Vec<Tactic>,
    /// The motive's letter, fresh to what is put into.
    pub(super) letter: &'static str,
    /// What is put into, with the places marked by the motive's letter.
    pub(super) marked: Node,
    /// The writer that knows the motive's letter, in the type the equation
    /// states it in.
    pub(super) inner: Writer<'w>,
    /// The whole number a place in a slot of whole numbers is written as.
    pub(super) slot: Option<super::super::templates::Num>,
    /// Whether the exponents are integers, converted to the claim's natural
    /// powers after (`PutExponents::int_exponent`).
    pub(super) int_exponent: bool,
    /// Whether the motive's letter is said whole, as the exponents are.
    pub(super) whole_was: bool,
}

/// What closes a putting once the motive has made the line the claim is
/// taken from (`Proof::substituted_as_written`).
pub(super) struct PutClosing {
    /// Whether a side holds a cast of a `toNat`, which `push_cast` moves
    /// only knowing the term is not negative.
    pub(super) cast_to_nat: bool,
    /// The lemmas for the identity elements the putting leaves and the
    /// claim drops.
    pub(super) dropped: Vec<&'static str>,
    /// The casts back of the whole numbers the step names, which take a cast
    /// of a `toNat` in the goal to the integer the line says.
    pub(super) backs: Vec<Printed>,
    /// The claim as Lean states it.
    pub(super) wanted: Option<Printed>,
}

impl PutClosing {
    /// The line the motive makes closed against the claim: by the casts
    /// pushed down to the letters, `exact_mod_cast` meeting the two.
    pub(super) fn close(&self, term: Printed) -> super::super::doc::Proof {
        use super::super::doc::Proof;
        use super::super::tactics as t;
        if self.cast_to_nat && self.dropped.is_empty() {
            return match self.backs.is_empty() {
                true => Proof::Term(term),
                false => Proof::By(Tactic::Seq(vec![
                    t::call(
                        "rw",
                        vec![TacticArg::Rules(
                            self.backs.iter().cloned().map(t::forwards).collect(),
                        )],
                    ),
                    Tactic::Exact(term),
                ])),
            };
        }
        let pushed = match self.dropped.is_empty() {
            true => t::push_cast(Some(t::at_h(true))),
            false => t::call(
                "push_cast",
                vec![
                    t::rules(self.dropped.iter().map(|l| t::lemma(l)).collect()),
                    t::at_h(true),
                ],
            ),
        };
        // A claim of numerals alone, `3 ∣ 1` in a contradiction, which
        // pushing the casts would work out by itself: the line put in the
        // goal and the whole worked out, true or false.
        if self.wanted.as_ref().is_some_and(no_letter) {
            return Proof::By(t::on_h(
                &term,
                vec![
                    t::call("revert", vec![TacticArg::Term(t::hyp("h"))]),
                    t::call("norm_num", vec![]),
                ],
            ));
        }
        Proof::By(t::on_h(&term, vec![pushed, t::exact_mod_cast(t::hyp("h"))]))
    }

    /// What the motive makes, `says`, written as Lean writes the claim: the
    /// claim itself, the term with nothing to push.
    pub(super) fn close_as(
        &self,
        term: Printed,
        says: Option<Printed>,
    ) -> super::super::doc::Proof {
        use super::super::doc::Proof;
        let as_written = self.dropped.is_empty()
            && !self.cast_to_nat
            && says.zip(self.wanted.as_ref()).is_some_and(|(s, w)| {
                s.text() == w.text()
                    && super::super::doc::forms::relation_type(&s)
                        == super::super::doc::forms::relation_type(w)
            });
        match as_written {
            true => Proof::Term(term),
            false => self.close(term),
        }
    }
}

/// A proof with these tactics before it, inside its `by`: a block of them
/// and then the proof's own tactic, each line indented under the `by`.
pub(super) fn haves_then(
    haves: Vec<Tactic>,
    proof: super::super::doc::Proof,
) -> super::super::doc::Proof {
    use super::super::doc::Proof;
    if haves.is_empty() {
        return proof;
    }
    let mut lines = haves;
    match proof {
        Proof::By(t) => lines.push(t),
        Proof::Term(t) => lines.push(Tactic::Exact(t)),
        Proof::Block(ts) => lines.extend(ts),
    }
    Proof::Block(lines)
}

/// A claim `s ∈ S`, S ℤ, ℚ or ℝ and s of a wider type, shown by an
/// equation, `name`, one side of which is in S already: that side is the
/// witness, and the equation, with the casts pushed in, its proof. None
/// where the claim or the equation is not so.
pub(super) fn member_by_equation(
    writer: &Writer,
    equation: &Node,
    name: &Printed,
    claim: &Node,
    ctx: &crate::matching::Context,
) -> Option<super::super::doc::Proof> {
    let [term, set] = claim.children.as_slice() else {
        return None;
    };
    if claim.notation() != crate::notations::MEMBERSHIP
        || set.notation() != crate::notations::NUMBER_SYSTEMS
        || equation.notation() != EQUALITY
    {
        return None;
    }
    let super::super::expr::System::Type(n) = super::super::expr::system_of(set)?
    else {
        return None;
    };
    if writer.carrier(term).built()? <= n {
        return None;
    }
    // The equation is of the claim's term: a = 1 shows nothing of √b + 1.
    if !equation
        .children
        .iter()
        .any(|side| crate::matching::alike_top(side, term, ctx))
    {
        return None;
    }
    equation.children.iter().enumerate().find_map(|(at, side)| {
        let fits = writer.carrier(side).built().is_some_and(|c| c <= n);
        if !fits || side.names().is_empty() && !writer.is_number(side) {
            return None;
        }
        let w = writer.number_fixed(side, n).built()?;
        // The witness `w` is the equation's side at `at`: the equation is
        // `↑w = s` as it stands where it is the left, turned where the
        // right; `exact_mod_cast` reads both with their casts moved alike.
        let faced = match at {
            0 => name.clone(),
            _ => super::super::tactics::symm(super::super::tactics::bracket(
                name.clone(),
            )),
        };
        let proof = super::super::tactics::by_term(super::super::doc::Proof::By(
            super::super::tactics::exact_mod_cast(faced),
        ));
        Some(super::super::doc::Proof::Term(
            super::super::expr::anonymous(vec![w, proof]),
        ))
    })
}

/// Why an exhibit declines where a fact it says of its values has no line
/// the checker found stating it (`fact_shown`).
pub(super) const UNSHOWN_FACT: &str =
    "an exhibit's fact no line the checker found states";

/// Why an instantiation declines where the membership of a value it gives
/// has no line the checker found supplying it (`value_guard`).
pub(super) const UNSUPPLIED_GUARD: &str =
    "an instantiated value's membership no line supplies";

/// A witness as Lean writes it, and the tactic that puts what a line says
/// of it in scope, where it is an integer a line gives.
pub(super) struct Witness {
    pub(super) term: Printed,
    pub(super) known: Option<Tactic>,
}

/// `proof`, after the tactics that put what lines say of the witnesses in
/// scope, `by …; exact proof`; `proof` itself where there are none.
pub(super) fn after_known(known: &[Tactic], proof: Printed) -> Printed {
    if known.is_empty() {
        return proof;
    }
    let mut tactics = known.to_vec();
    tactics.push(Tactic::Exact(proof));
    super::super::tactics::by_term(super::super::doc::Proof::By(Tactic::Seq(tactics)))
}

/// A function the header lets, applied in a step citing an item
/// (`Proof::header_functions_applied`).
#[derive(Clone)]
pub(super) struct HeaderApplied {
    /// The define, as `put_define` writes it out.
    pub(super) define: CitedDefine,
    /// Its equation at the argument, `hD1 _ hH2`.
    pub(super) equation: Printed,
}

/// A define a step cites: its letter, the term it names, and the Lean name
/// of its equation.
#[derive(Clone)]
pub(super) struct CitedDefine {
    pub(super) name: Node,
    pub(super) value: Node,
    pub(super) proof: String,
    /// The argument of a function's define, the j of q(j) = F(j)², which
    /// each application q(a) puts a for; None for a define of a term.
    pub(super) param: Option<String>,
}

/// The proof of `d ≠ 0` from a line `proof` stating, in Lean, `d ≠ 0`, `0 ≠
/// d`, `0 < d`, `d < 0`, `d > 0` or `0 > d`: the line, its `symm`, `ne'` or
/// `ne`. None of a statement of another form.
pub(super) fn nonzero_turned(proof: &Printed, says: &Printed) -> Option<Printed> {
    use super::super::doc::TermKind;
    fn zero(p: &Printed) -> bool {
        match &bare_term(p).kind {
            TermKind::Numeral(n) => n == "0",
            TermKind::Cast { inner, .. } => zero(inner),
            _ => false,
        }
    }
    let TermKind::Infix { op, lhs, rhs } = &bare_term(says).kind else {
        return None;
    };
    let field = match (op.symbol, zero(lhs), zero(rhs)) {
        ("≠", false, true) => None,
        ("≠", true, false) => Some("symm"),
        ("<", true, false) | (">", false, true) => Some("ne'"),
        ("<", false, true) | (">", true, false) => Some("ne"),
        _ => return None,
    };
    Some(match field {
        Some(f) => fields(proof.clone(), &[f]),
        None => proof.clone(),
    })
}

/// Whether a line puts a term of a type wider than ℤ in ℕ, x ∈ ℕ of a real
/// x, which Lean states by its witness, `∃ m : ℤ, 0 < m ∧ (m : ℝ) = x`.
pub(super) fn natural_witnessed(line: &Node, writer: &Writer) -> bool {
    let (crate::notations::MEMBERSHIP, [x, set]) =
        (line.notation(), line.children.as_slice())
    else {
        return false;
    };
    matches!(
        super::super::expr::system_of(set),
        Some(super::super::expr::System::Positive)
    ) && writer
        .carrier(x)
        .built()
        .is_some_and(|c| c > super::super::templates::Num::Int)
}

/// The proof of `x ≠ 0` from a line `proof` saying x is a natural number by
/// its witness (`natural_witnessed`): `by obtain ⟨m, hm, hx⟩ := proof; rw
/// [← hx]; positivity`, the witness above 0 by `hm`.
pub(super) fn unwitnessed_nonzero(proof: &Printed) -> Printed {
    use super::super::tactics as t;
    let by = super::super::doc::Proof::By(Tactic::Seq(vec![
        Tactic::Obtain {
            names: vec!["m".to_string(), "hm".to_string(), "hx".to_string()],
            says: None,
            from: proof.clone(),
        },
        t::call(
            "rw",
            vec![TacticArg::Rules(vec![t::backwards(t::hyp("hx"))])],
        ),
        t::call("positivity", vec![]),
    ]));
    t::bracket(t::by_term(by))
}

/// Whether a term is a number system or a range of integers, which a
/// function's define may run its argument over.
pub(super) fn system_or_range(n: &Node) -> bool {
    matches!(
        n.notation(),
        crate::notations::NUMBER_SYSTEMS | crate::notations::INTEGER_RANGE
    )
}

/// The functions a term applies, f of f(x).
pub(super) fn applied_names(node: &Node) -> Vec<String> {
    node.walk()
        .iter()
        .filter(|n| n.notation() == crate::notations::APPLICATION)
        .filter_map(|n| n.children.first())
        .filter(|f| f.is_name())
        .map(|f| f.text.to_string())
        .collect()
}

/// A function's define as the checker reads its line apart
/// (`Proof::function_read`).
pub(super) struct FunctionRead {
    /// The set the argument runs over, [0, 1] of `for x ∈ [0, 1]`.
    pub(super) domain: Node,
    /// The value at the argument, x^(2n) of f(x) = x^(2n).
    pub(super) body: Node,
}

/// A place a step's defines are written out at, a line the step uses or the
/// goal, with what it says there.
pub(super) struct RewriteAt {
    pub(super) at: super::super::doc::Location,
    pub(super) said: Vec<Node>,
    /// What it says as Lean states it, where the writer has it.
    pub(super) stated: Vec<Printed>,
}

impl RewriteAt {
    /// Whether what Lean states there holds a cast, which is pushed in with
    /// the defines' (`push_cast` changes nothing where none moves).
    pub(super) fn cast(&self) -> bool {
        self.stated.iter().any(holds_cast)
    }

    /// Whether Lean's statement there names `name`, a define's letter or
    /// function; F(x) ∈ ℝ, stated `True`, does not. A place whose statement
    /// the writer does not have is taken as the page writes it.
    pub(super) fn names(&self, name: &str) -> bool {
        self.stated.is_empty()
            || self.stated.iter().any(|s| {
                s.walk().iter().any(
                    |p| matches!(&p.kind, super::super::doc::TermKind::Letter(n) if n == name),
                )
            })
    }

    /// Whether Lean writes `term` in what it states there.
    pub(super) fn writes(&self, term: &Printed) -> bool {
        let want = term.untyped();
        self.stated
            .iter()
            .any(|s| s.walk().iter().any(|p| p.untyped() == want))
    }
}

/// The tactic lines that write the defines out at `at`, the lines the step
/// uses and the goal (`Proof::rewritten_at`): at each place, the defines
/// whose names it writes, `simp only [hD1] at s3`; then the casts pushed in
/// at each place whose statement holds one, or to which a define's value
/// brings one as Lean writes it (`writer`). None where no define is cited.
pub(super) fn written_out(
    defines: &[CitedDefine],
    at: &[RewriteAt],
    writer: &Writer,
) -> Vec<Tactic> {
    written_out_as(defines, at, writer, true)
}

/// `written_out`, the casts pushed in after where `push`; not where the
/// rewrite leaves a claim's two sides one term, which it closes.
pub(super) fn written_out_as(
    defines: &[CitedDefine],
    at: &[RewriteAt],
    writer: &Writer,
    push: bool,
) -> Vec<Tactic> {
    use super::super::tactics as t;
    if defines.is_empty() {
        return Vec::new();
    }
    let cast_in = |d: &CitedDefine| match writer.carrier(&d.value) {
        Route::Built(n) => writer.number(&d.value, n).built().is_none_or(|p| {
            p.walk()
                .iter()
                .any(|c| matches!(c.kind, super::super::doc::TermKind::Cast { .. }))
        }),
        Route::Declined(_) => true,
    };
    // Places by the defines they name, so that places naming the same take
    // one line; and the places casts are pushed in at.
    let mut groups: Vec<(Vec<usize>, Vec<super::super::doc::Location>)> = Vec::new();
    let mut pushed: Vec<super::super::doc::Location> = Vec::new();
    for place in at {
        // The defines the place names, and those their values name in turn,
        // which writing them out brings in: v of y + ω₁·T brings ω₁.
        // A function's define is written out only where the function is
        // applied, f(x): its equation rewrites f(x), not f standing alone.
        // The place's own names are those Lean's statement of it keeps
        // (`RewriteAt::names`).
        let mut names: Vec<String> = place
            .said
            .iter()
            .flat_map(|n| n.names())
            .filter(|x| place.names(x))
            .collect();
        let mut applied: Vec<String> = place
            .said
            .iter()
            .flat_map(applied_names)
            .filter(|x| place.names(x))
            .collect();
        let mut named: Vec<usize> = Vec::new();
        loop {
            let more: Vec<usize> = defines
                .iter()
                .enumerate()
                .filter(|(i, d)| {
                    let written = match d.param {
                        Some(_) => &applied,
                        None => &names,
                    };
                    !named.contains(i)
                        && written.iter().any(|x| x.as_str() == &*d.name.text)
                })
                .map(|(i, _)| i)
                .collect();
            if more.is_empty() {
                break;
            }
            for &i in &more {
                names.extend(defines[i].value.names());
                applied.extend(applied_names(&defines[i].value));
            }
            named.extend(more);
        }
        named.sort();
        if named.is_empty() {
            continue;
        }
        if place.cast() || named.iter().any(|&i| cast_in(&defines[i])) {
            pushed.push(place.at.clone());
        }
        match groups.iter_mut().find(|(g, _)| *g == named) {
            Some((_, locs)) => locs.push(place.at.clone()),
            None => groups.push((named, vec![place.at.clone()])),
        }
    }
    let mut out = Vec::new();
    for (named, locs) in groups {
        let rewrites = named
            .iter()
            .map(|&i| t::forwards(t::hyp(&defines[i].proof)))
            .collect();
        out.push(t::simp_only(
            false,
            None,
            rewrites,
            Some(TacticArg::At(locs)),
        ));
    }
    if push && !pushed.is_empty() {
        out.push(t::push_cast(Some(TacticArg::At(pushed))));
    }
    out
}

/// `node` with `to` put for each part that is `from`, the two compared as
/// the grammar prints them.
/// Whether putting one side of `equation` for the other in the left side of
/// `claim`, an equation, gives its right side.
pub(super) fn makes_claim(
    equation: &Node,
    claim: &Node,
    grammar: &crate::formula::Grammar,
) -> bool {
    let (Some([from, to]), Some([left, right])) = (
        equation.children.as_slice().first_chunk::<2>(),
        claim.children.as_slice().first_chunk::<2>(),
    ) else {
        return false;
    };
    let want = grammar.print(right);
    [(from, to), (to, from)]
        .iter()
        .any(|(a, b)| grammar.print(&put_term(left, a, b, grammar)) == want)
}

pub(super) fn put_term(
    node: &Node,
    from: &Node,
    to: &Node,
    grammar: &crate::formula::Grammar,
) -> Node {
    if grammar.print(node) == grammar.print(from) {
        return to.clone();
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| put_term(c, from, to, grammar))
            .collect(),
    )
}

/// `node` with `value` put for each place the letter `name` stands.
pub(super) fn put_for(node: &Node, name: &Node, value: &Node) -> Node {
    if node.is_name() && node.text == name.text {
        return value.clone();
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| put_for(c, name, value))
            .collect(),
    )
}

/// How many statements an "or" joins, however it groups them.
pub(super) fn disjuncts(node: &Node) -> usize {
    if node.notation() == crate::notations::DISJUNCTION {
        node.children.iter().map(disjuncts).sum()
    } else {
        1
    }
}

/// An `rcases` pattern for an "or" as its tree groups it, each disjunct
/// named in turn from `names`: `(C1 | C2) | C3` for (a ∨ b) ∨ c.
pub(super) fn or_pattern(
    node: &Node,
    names: &mut std::slice::Iter<'_, String>,
) -> super::super::doc::Pattern {
    use super::super::doc::Pattern;
    if let ([left, right], crate::notations::DISJUNCTION) =
        (node.children.as_slice(), node.notation())
    {
        let l = or_pattern(left, names);
        let r = or_pattern(right, names);
        return Pattern::Or(Box::new(l), Box::new(r));
    }
    Pattern::Name(names.next().cloned().unwrap_or_else(|| "_".to_string()))
}

/// The cases as one "or", each bracketed: `(a) ∨ (b) ∨ (c)`.
pub(super) fn cases_said(cases: Vec<Printed>) -> Printed {
    let bracketed = cases
        .into_iter()
        .map(super::super::tactics::bracket)
        .collect();
    match super::super::doc::Op::of("∨")
        .and_then(|or| super::super::expr::joined(or, bracketed, 0))
    {
        Some(all) => all,
        None => Printed::truth(),
    }
}

/// The cases named in turn, read from the right: `a | b | c`.
pub(super) fn cases_pattern(names: &[String]) -> super::super::doc::Pattern {
    use super::super::doc::Pattern;
    match names {
        [] => Pattern::Name("_".to_string()),
        [one] => Pattern::Name(one.clone()),
        [first, rest @ ..] => Pattern::Or(
            Box::new(Pattern::Name(first.clone())),
            Box::new(cases_pattern(rest)),
        ),
    }
}

/// The lines a step cites anywhere in its reason: its own references, the
/// line it substitutes into, and those its calculation's rows cite, by a
/// reason of their own or alone.
pub(super) fn step_cited_refs(step: &crate::corpus::Step, path: &str) -> Vec<String> {
    let mut out: Vec<String> = step.just.refs.clone();
    let into = |j: &Justification| j.into.as_ref().map(|p| p.named().to_string());
    out.extend(into(&step.just));
    if let Some(Ok(chain)) = crate::corpus::proof::chain(&step.just, path) {
        for line in &chain.lines {
            match &line.reason {
                Some(r) => {
                    if let Ok(by) = &r.by {
                        out.extend(by.refs.iter().cloned());
                        out.extend(into(by));
                    }
                }
                None => {
                    if let Some(cited) = crate::corpus::proof::chain_cited(&line.cite) {
                        out.push(cited);
                    }
                }
            }
        }
    }
    let mut seen = std::collections::BTreeSet::new();
    out.retain(|r| seen.insert(r.clone()));
    out
}

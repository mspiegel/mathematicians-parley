//! What the checker decides about a theorem, once, for itself and for the
//! build: the block each step stands in and which part of it, each block's
//! steps and its last, the place each define is written in, the sort of
//! each name, the functions typed at each step, and the problems it finds.
//!
//! The build is handed this rather than working it out again as it walks
//! the proof, so the two cannot read one proof two ways.

use std::collections::BTreeSet;
use std::sync::Arc;

use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::citing::bounds::SaidBounds;
use crate::citing::finite::{FiniteSets, SaidFinite};
use crate::citing::number_sets::Between;
use crate::citing::things::ThingTypes;
use crate::citing::{
    Concluded, Group, HypothesisAt, Implication, Introduced, SaidOnceFact, Want,
};
use crate::corpus::{Step, StepPlace, Theorem};
use crate::formula::node::ByShape;
use crate::formula::page::Sentence;
use crate::formula::symbol::Symbol;
use crate::formula::{Node, Sorts};
use crate::matching::{Binding, Definitions, Flip, Meeting, SubstitutionPlaces};
use crate::methods::pairs::Coordinate;
use crate::notations::{THERE_IS, THERE_IS_SOME};
use crate::outcome::{Checked, Problem};
use crate::rules::System;
use crate::sorts::CitedStatement;

/// Where a step or a define stands: directly in a block, and in which part
/// of it where the block has parts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Place {
    /// The block, by its index in `CheckedTheorem::blocks`.
    pub block: usize,
    /// The part, counted from 0, of a block with parts.
    pub part: Option<usize>,
}

/// A step that owns a block: what it opens, and what stands in it.
#[derive(Clone, Debug)]
pub struct Block {
    /// The owning step, by its index in the theorem's steps.
    pub owner: usize,
    /// Where the owner itself stands; None at the proof's outermost level.
    pub within: Option<Place>,
    /// The steps standing directly in the block, in the order written.
    pub children: Vec<usize>,
    /// What each part of an induction, a `cases` block or a `proof` block
    /// owes, which its last step is to claim (`SYNTAX.md`, the methods that
    /// open a block); none for another block.
    pub owes: Vec<Owed>,
}

/// What one part of a block owes: the sentences its last step is to claim,
/// read with no define written out.
#[derive(Clone, Debug)]
pub struct Owed {
    /// The part, counted from 0; None for a `proof` block, which has none.
    pub part: Option<usize>,
    pub claim: Vec<Node>,
    /// What the part's last step ends on, where the part names a method on
    /// a `by` line (`Step::by_lines`): under `by proof`, the claim with the
    /// part's inner `let` and `assume` lines taken off; empty under `by
    /// contradiction`, whose last step contradicts a line. The claim itself
    /// for a part with no `by` line.
    pub ends: Vec<Node>,
    /// The same, read as the page writes it, with its defines kept and in
    /// the order written: the goal a backend has when the part ends, the
    /// claim it states with the block's lines taken off.
    pub written: Vec<Node>,
}

impl Block {
    /// The block's last step of its own: the last child, never a step of a
    /// block inside it.
    pub fn last(&self) -> Option<usize> {
        self.children.last().copied()
    }

    /// What part `part` ends on as the page writes it (`Owed::written`);
    /// None where the block records nothing owed, as a contradiction block
    /// does.
    pub fn ends_written(&self, part: Option<usize>) -> Option<&[Node]> {
        self.owes
            .iter()
            .find(|o| o.part == part)
            .map(|o| o.written.as_slice())
    }
}

impl CheckedTheorem {
    /// The last step of its own that part `part` of block `block` holds.
    pub fn last_in(&self, block: usize, part: Option<usize>) -> Option<usize> {
        self.blocks[block]
            .children
            .iter()
            .rev()
            .copied()
            .find(|&c| self.places[c].is_some_and(|p| p.part == part))
    }
}

/// Where a sentence is written and what it says: the line, and the text.
/// A theorem's lines are its own, so within one theorem this names one
/// sentence of its page.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PartKey {
    pub line: usize,
    pub text: String,
}

impl PartKey {
    pub fn of(sentence: &Sentence) -> PartKey {
        PartKey {
            line: sentence.line(),
            text: sentence.text().to_string(),
        }
    }
}

/// Every formula on a theorem's page as the checker read it: each
/// sentence's tree, by where it is written. The build takes a sentence of
/// the page from here and never parses one again, so the two read one
/// proof one way.
#[derive(Clone, Debug, Default)]
pub struct PageReading {
    read: FxHashMap<PartKey, Node>,
}

impl PageReading {
    pub fn new(read: FxHashMap<PartKey, Node>) -> PageReading {
        PageReading { read }
    }

    /// The tree of a sentence of the page, as the checker read it.
    pub fn get(&self, sentence: &Sentence) -> Option<&Node> {
        self.read.get(&PartKey::of(sentence))
    }

    /// Every sentence read, in no order, for a record printed in review.
    pub fn entries(&self) -> impl Iterator<Item = (&PartKey, &Node)> {
        self.read.iter()
    }
}

/// Where a sentence of an item is written and what it says: its file, its
/// line and its text.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ItemKey {
    pub path: String,
    pub line: usize,
    pub text: String,
}

impl ItemKey {
    pub fn of(sentence: &Sentence) -> ItemKey {
        ItemKey {
            path: sentence.path().to_string(),
            line: sentence.line(),
            text: sentence.text().to_string(),
        }
    }
}

/// Every sentence of every item a citation may name, a record of the
/// library or a theorem of the corpus, read once as the item means it, with
/// its own sorts (`citing::Library::item_readings`), by where it is
/// written. The build takes an item's sentence from here, so it reads what
/// it cites as the checker does. A sentence that does not read keeps its
/// problem, which the build reports where it asks for it.
#[derive(Clone, Debug, Default)]
pub struct ItemReading {
    read: FxHashMap<ItemKey, Checked<Node>>,
}

impl ItemReading {
    /// A sentence of an item, read, kept.
    pub fn keep(&mut self, sentence: &Sentence, read: Checked<Node>) {
        self.read.entry(ItemKey::of(sentence)).or_insert(read);
    }

    /// The reading of a sentence of an item, where the checker read one.
    pub fn get(&self, sentence: &Sentence) -> Option<&Checked<Node>> {
        self.read.get(&ItemKey::of(sentence))
    }
}

/// What the checker read of every item a citation may name, once for the
/// corpus, which the build cites from and never reads again.
#[derive(Default)]
pub struct LibraryReading {
    /// The sorts of every item record, by its place in the records
    /// (`sorts::sorts_of_records`).
    pub record_sorts: IndexMap<usize, Sorts>,
    /// How a citation reads each proved theorem's statement, by its full
    /// name (`sorts::cited_statement`).
    pub cited: IndexMap<String, CitedStatement>,
    /// Each item's groups, by its full name, a record's and a proved
    /// theorem's (`citing::Library::groups`).
    pub groups: IndexMap<String, Option<Arc<Vec<Group>>>>,
    /// What each item's function-type `let` lines say, `t : {a, …, b} → ℝ`,
    /// by its full name, which its groups leave out, each with where the
    /// item writes it (`citing::Library::function_type_lines`).
    pub function_types: IndexMap<String, Vec<Want>>,
    /// What each group of each item says of its terms, its phrases written
    /// out, by the item's full name and the group's place
    /// (`checker::written::item_facts`).
    pub item_facts: IndexMap<String, Vec<GroupFacts>>,
    /// The set each property an item's `let` lines name is of, read, by
    /// the item's full name and the property's letter: ℕ of `P be a
    /// property of the elements of ℕ`.
    pub property_domains: IndexMap<String, IndexMap<String, Node>>,
}

/// What one group of an item says of its terms, read as a theorem's lines
/// are (`LibraryReading::item_facts`).
#[derive(Clone, Debug)]
pub struct GroupFacts {
    /// What its hypotheses bound below (`citing::bounds`).
    pub bounds: SaidBounds,
    /// The sets its hypotheses make finite (`citing::finite::said_finite`).
    pub finite: SaidFinite,
    /// For each sentence it concludes, the number system each set letter of
    /// numbers holds by the hypotheses and that sentence
    /// (`citing::number_sets::set_letter_systems`).
    pub set_systems: Vec<IndexMap<String, System>>,
    /// The function letters its function-type lines and hypotheses give a
    /// type between sets of numbers, `t : {a, …, b} → ℝ`, with the systems
    /// of the domain and the codomain, as a theorem's are
    /// (`CheckedTheorem::function_systems`).
    pub function_systems: IndexMap<String, Between>,
}

/// A condition of a define by cases that a step citing it passes: `t = c`
/// of "F(t) = 0 if t = c, f(t) otherwise".
#[derive(Clone, Debug)]
pub struct PassedCondition {
    /// Whether it holds, giving its case, or fails, passing to the next.
    pub holds: bool,
    /// The fact that says so, where a line the step cites states it; None
    /// where it comes from a requires line or is not found in one.
    pub said_by: Option<FirstAt>,
}

/// The case of a define by cases a step takes, as the checker read it.
#[derive(Clone, Debug)]
pub struct TakenCase {
    /// The conditions passed to reach it, in the define's order: each
    /// failing, for the cases before it, and the last holding, unless the
    /// case is the one written `otherwise`.
    pub passed: Vec<PassedCondition>,
    /// Whether the define's name is on the claim's right side, so the case
    /// is read off the right and meets the left; false where it is on the
    /// left.
    pub turned: bool,
    /// How the case's value meets the claim's other side (`Known::alike_how`):
    /// as it stands, or with arithmetic left; None where they met only as
    /// `Known::alike` reads them.
    pub meeting: Option<Meeting>,
}

/// A theorem as the checker reads it.
#[derive(Clone, Debug, Default)]
pub struct CheckedTheorem {
    /// Every formula on the page, read.
    pub page: PageReading,
    /// Every sentence of every item the corpus may cite, read: one reading
    /// for the corpus, shared by each theorem's record.
    pub items: Arc<ItemReading>,
    /// What each definition the theorem sees from outside it stands for,
    /// written out where it was defined (`sorts::file_definitions`).
    pub outside: Definitions,
    /// What the theorem's statement is read with, written out: the
    /// definitions from outside it and those of its header, read with its
    /// sorts (`sorts::statement_definitions`).
    pub statement_definitions: Definitions,
    pub blocks: Vec<Block>,
    /// Where each step stands, by its index in the theorem's steps; None at
    /// the outermost level.
    pub places: Vec<Option<Place>>,
    /// Where each of the theorem's defines stands, by its index in
    /// `Theorem::defines`: the place of the first step written after it,
    /// which is where the build opens it.
    pub defines: Vec<Option<Place>>,
    /// The sort of each name, as the theorem's one reading settles it, its
    /// citations fitted as it goes.
    pub sorts: Sorts,
    /// What the checker reports in the theorem, in the order it finds it;
    /// the build builds a theorem only where this is empty.
    pub problems: Vec<Problem>,
    /// The function types the lines in scope at each step say, `v : {0, …,
    /// n} → V`, by the step's index (`typed_in_scope`): what a citation of
    /// an item over a function is read with (`citing::typed_seed`).
    pub typed: Vec<Vec<Node>>,
    /// The sums each step writes that the page says are numbers once, by
    /// their terms at every index, as written, by the step's index
    /// (`library::sums_said_once`): what the build proves a member of ℝ or
    /// ℂ without a line saying so.
    pub said_sums: Vec<Vec<Node>>,
    /// The sets the theorem's hypotheses, defines and bound letters make
    /// finite (`citing::finite::said_finite`): what a backend that writes a
    /// count by whether its set is finite asks with `citing::finite::is_finite`.
    pub said_finite: SaidFinite,
    /// The number system each set letter of numbers holds, D of `D ⊆ ℝ` or
    /// c of `{1, …, i} ∖ c` (`citing::number_sets::set_letter_systems`):
    /// what a backend whose sets are typed gives the letter.
    pub set_systems: IndexMap<String, System>,
    /// Which of the theorem's sets, members and maps' sides hold things of
    /// one type, read over every line of its page in order
    /// (`citing::things::ThingTypes`): A and B of `f : A → B` apart, C of
    /// `C ⊆ A` with A. What a backend whose sets are typed gives each its
    /// type variable by.
    pub thing_types: ThingTypes,
    /// The number system each letter in scope at a step is introduced in,
    /// by the step's index (`library::introduced`): the narrower of two
    /// where a later line narrows it, q ∈ ℕ₀ of a q let in ℤ. What the
    /// said-once walk reads letters by (`citing::reason`), so that a backend
    /// asking it of a term asks with the checker's letters.
    pub introduced: Vec<Introduced>,
    /// Where each letter of `introduced` is put in its number system, by
    /// the step's index (`library::introduced_places`): the line, and the
    /// sentence and part of it, that last says the letter's membership, as
    /// a citation of that line is placed. A letter of a `let` with no label
    /// has no place.
    pub introduced_at: Vec<IndexMap<String, FirstAt>>,
    /// The letters in scope introduced as points, by the step's index
    /// (`library::points_introduced`): `let A be a point`, or a line saying
    /// A ∈ 𝔼². A point is in no number system the page writes; a backend
    /// that encodes points as complex numbers reads them here.
    pub points_at: Vec<BTreeSet<String>>,
    /// Each step's citation of an item, by the step's index; None for a step
    /// that cites none, or whose citation no group of the item reads, which
    /// the checker reports.
    pub cited: Vec<Option<Cited>>,
    /// Each requires line's citation of an item, by the line it is on, read
    /// as the step the line would be (`requires_as_step`).
    pub cited_requires: IndexMap<usize, Cited>,
    /// The relation each line a `transitivity` step cites gives its chain,
    /// in the order cited, by the line of its justification: the line's
    /// own, or of a line saying several, the one that meets the chain
    /// (`ChainLink`).
    pub links: IndexMap<usize, Chain>,
    /// What each `inequalities` step, each requires line whose reason is
    /// `inequalities`, and each requires line naming one manipulation rests
    /// on, by the line of its justification (`formulas::order_steps`). A
    /// step whose facts do not all stand where a backend can name them is
    /// left out.
    pub orders: IndexMap<usize, OrderStep>,
    /// How each `antisymmetry` step's lines make its equation, by the line
    /// of its justification (`formulas::antisymmetries`).
    pub antisymmetric: IndexMap<usize, Antisymmetric>,
    /// Where each part of each `join` step's claim stands among the lines
    /// it cites, by the line of its justification: for each sentence of the
    /// claim, each of its parts joined by "and", in order
    /// (`citations::join_places`). A step with a part found in no one line,
    /// one said only with a define's name read out, is left out.
    pub joined: IndexMap<usize, Vec<Vec<JoinedPart>>>,
    /// Of each `join` step in `joined`, each run of its claim's parts, a
    /// sentence or an "and" of several parts, that one line it cites states
    /// whole, by the line of its justification (`citations::join_wholes`):
    /// the page joins that line as it stands.
    pub joined_wholes: IndexMap<usize, Vec<JoinedWhole>>,
    /// Of each `join` step in `joined`, each part of its claim as the page
    /// writes it, in the order `joined` places them
    /// (`citations::join_claim_parts`): a phrase whose meaning is an "and",
    /// `a is odd`, is one part.
    pub joined_claim: IndexMap<usize, Vec<Node>>,
    /// What each `exhibit` step shows, by the line of its justification: for each
    /// sentence of its claim, the values of its "there is" and where each
    /// fact it says of them stands (`citations::exhibit_values`).
    pub exhibited: IndexMap<usize, Vec<Option<Exhibit>>>,
    /// How each obtain step's sentences after its memberships are the parts
    /// of the "there is" it obtains from, by the line of its justification
    /// (`citations::obtained_parts`).
    pub obtained_parts: IndexMap<usize, Vec<ObtainedPart>>,
    /// Where on the line it names the "there is" each obtain step that
    /// cites no item obtains from stands, by the line of its justification:
    /// the line's one "there is" among what it says, a sentence, a part of
    /// one, or a "for all" read at a block's letter (`Known::says`); or, of
    /// a line of one sentence that says it otherwise, "there is a ∈ A" with
    /// no body, that sentence.
    pub obtained_from: IndexMap<usize, FirstAt>,
    /// How each instantiation's instance reaches its claim, a step's, a
    /// calculation row's or a requires line's, by the line of its
    /// justification
    /// (`citations::instantiations`).
    pub instantiated: IndexMap<usize, Instantiated>,
    /// How the lines give each `restate` step's claim of one sentence, and
    /// each requires line reasoned from lines alone (`Restated`), by the
    /// line of its justification (`citations::restatements`).
    pub restated: IndexMap<usize, Restated>,
    /// How each calculation link citing a define, and each step whose reason
    /// is defines, meets the defines written out: its equation's two sides
    /// once each define's name is its value, a "for all"'s at its body; None
    /// where they do not meet and arithmetic is left. By the link's or the
    /// step's line (`formulas::define_link_meetings`).
    pub define_links: IndexMap<usize, Option<Meeting>>,
    /// Of each step citing a define by cases whose value it claims in one
    /// case, how it reaches that case and meets it. By the step's line
    /// (`formulas::define_cases`).
    pub define_cases: IndexMap<usize, TakenCase>,
    /// Of each step citing a define of a name, a function or a recursion
    /// whose claim is one equation, which side has the define at its head
    /// (`formulas::define_sides`), by the step's line. A step that claims a
    /// function on a set is left out.
    pub define_sides: IndexMap<usize, DefineSide>,
    /// Of each step citing a function a define lets on a domain, `H(x) for
    /// x ∈ A ∪ B`, or substituting the define's equation at an argument,
    /// what says the argument of each application it makes of the function is
    /// in that domain, in the order the applications stand in the claim or
    /// the equation. By the step's line (`citations::define_domains`).
    pub define_domains: IndexMap<usize, Vec<AppliedDomain>>,
    /// Of each step of a method or an item citing a function a define lets
    /// on a domain, each application whose domain the step asks, with what
    /// says the
    /// argument is in it: q(a) of a transitivity from D1, a ∈ ℕ on the `let`
    /// line. By the step's line (`citations::applied_domains`).
    pub applied_domains: IndexMap<usize, Vec<AppliedDomain>>,
    /// Where in the line each calculation link cites the link stands, by
    /// the link's line (`formulas::link_places`). A link read off a chain,
    /// a = c of a = b = c, is placed at the chain's sentence with the pair it
    /// reads as `written`.
    pub link_places: IndexMap<usize, FirstAt>,
    /// How the line met each calculation link it does not state as written,
    /// as a restatement's (`Restated::Stated`): `F(0) + G(0) = G(1)` of `G(0 + 1) = F(0) +
    /// G(0)`. By the link's line (`formulas::link_places`).
    pub link_meetings: IndexMap<usize, Meeting>,
    /// Which way each calculation link that cites a line faces what the line
    /// says, an equation of the line's turned round where the link writes
    /// its sides the other way (`citations::facing_of`), by the link's line
    /// (`formulas::link_places`). None where the line says no equation or no
    /// side meets; left out where the link is not placed.
    pub link_facings: IndexMap<usize, Option<Facing>>,
    /// Which way each calculation link citing a define of a name, and each
    /// step citing one, faces the define's equation, by the link's line or
    /// the line of the step's justification (`formulas::define_facings`);
    /// left out where no side meets, and for a define of a function or a
    /// recursion, which says no one equation.
    pub define_facings: IndexMap<usize, Facing>,
    /// How each `substitute` step and calculation row writing no rows makes
    /// its claim, by the line of its justification; none where the
    /// equation is put at places only a standard order of the trees finds,
    /// or an identity element is dropped on the way
    /// (`citations::substitutions`).
    pub substituted: IndexMap<usize, Substituted>,
    /// How each row of a `substitute` step after the first makes the row:
    /// the change its reason proves put into the row above, by the line of
    /// the row's reason (`citations::row_substitutions`). Apart from
    /// `substituted`, which has under that line how the reason itself makes
    /// the change.
    pub substituted_rows: IndexMap<usize, Substituted>,
    /// Of a substitution into a line's sentences together whose claim has
    /// as many sentences, each claim sentence as made from the line's
    /// sentence in its place, by the line of the justification and the
    /// sentence's place (`citations::sentence_substitutions`): a backend
    /// that names the sentences apart puts the equation into each.
    pub substituted_sentences: IndexMap<(usize, usize), Substituted>,
    /// What each of the theorem's `let` lines asserts that the page does not
    /// read as a formula, `f : A → B be one-to-one` as `f : A → B is
    /// one-to-one`, by the hypothesis's index; empty for any other line
    /// (`library::let_assertions`).
    pub asserted: Vec<Vec<Node>>,
    /// The same of each `let` opening a block, `let X ⊆ A`, by the line it
    /// is on (`library::opener_assertions`).
    pub opener_asserted: IndexMap<usize, Vec<Node>>,
    /// How each contradiction's supposition stands to what it shows, by the
    /// line its `suppose` is on (`formulas::suppositions`).
    pub supposed: IndexMap<usize, Supposition>,
    /// The two lines each step written `contradicting N` that ends a block
    /// or a case closes it on, by the line of its justification
    /// (`formulas::contradictions`).
    pub contradicted: IndexMap<usize, Contradicted>,
    /// What each `cases` step splits, by the line of its justification
    /// (`formulas::cases_splits`).
    pub cases_from: IndexMap<usize, CasesSplit>,
    /// How each step that ends a block, a part of one or the proof meets
    /// what it owes, by the line of its justification: one meeting for each
    /// part of its "and" in order (`formulas::ended_meetings`).
    pub ends_met: IndexMap<usize, Vec<Meeting>>,
    /// How each calculation's first and last terms meet the step's claim,
    /// by the line of its justification: permuted where a listed set's
    /// members stand in another order (`formulas::calculation_meetings`).
    pub calculation_ends: IndexMap<usize, Meeting>,
    /// Where the first row of each `substitute` step with rows stands in the
    /// line it cites, and how its last row meets the step's claim, by the
    /// line of the step's justification (`formulas::substitute_row_ends`).
    pub substitute_ends: IndexMap<usize, RowEnds>,
    /// Each term a step puts where a notation asks a number system, a of
    /// a ≡ b (mod n) in ℤ, with how the step shows it is in that system
    /// (`formulas::check_place_systems`), by the step's index: so that a
    /// backend proves the membership as the check found it.
    pub places_shown: Vec<Vec<PlaceShown>>,
    /// Each claim the `membership` method proves, by the line its reason
    /// is on, whose term is in its system beside an equation a line it
    /// names says (`ShownBy::Beside`): a^(p − 1) ∈ ℤ from a^(p − 1) =
    /// a^(p − 2)·a and a^(p − 2) ∈ ℤ. A backend proves it the same way.
    pub members_shown: IndexMap<usize, PlaceShown>,
    /// Each claim the `inspection` method decides holds, a step's or a
    /// requires line's, by the line its reason is on: the case that decided
    /// it (`methods::inspection::Case`), and for an "or" of what a term is,
    /// the cited line whose membership it is read against. A backend
    /// proves each case one way: r = 0 or r = 1 or r = 2 from r ∈ {0, …, 2}
    /// by the range's bounds.
    pub inspected: IndexMap<usize, Inspection>,
    /// Each claim that two pairs differ, by the line its reason is on, with
    /// the coordinate its method found them apart at
    /// (`formulas::pairs_apart`): the first of (1, 1) ≠ (2, 3) by
    /// arithmetic, the second of (a, b) ≠ (c, d) by algebra from b ≠ d. A
    /// backend proves the pairs apart there.
    pub pairs_apart: IndexMap<usize, Coordinate>,
    /// The parts of the terms a reason's claim and lines write that the
    /// lines it names put in a number system, each with how, by the line
    /// the reason is on: a step's, or a requires line's
    /// (`formulas::held_by_lines`). The said-once walk takes a term apart
    /// into its parts and reads each here, so that a backend names a part
    /// whole from the line the check found, m of m² from `m ∈ ℕ`, and from
    /// no line the reason does not name.
    pub held_by_lines: IndexMap<usize, Vec<HeldByLines>>,
    /// The notations whose parts stand in no order (`commutes any order`)
    /// that a reason's claim and the lines it names write with their parts
    /// in more than one order, |AB| in one and |BA| in another, by the line
    /// the reason is on: a step's, or a requires line's
    /// (`formulas::commuted_by_lines`). The reason reads them as one term;
    /// a backend turns each by its own lemma where it works on the terms
    /// as written.
    pub commuted_by_lines: IndexMap<usize, Vec<String>>,
    /// Each part an `algebra` reason divides by, with why it is not zero,
    /// by the line the reason is on: a step's, a requires line's or a
    /// calculation row's (`formulas::divided_by`). A backend clears the
    /// divisions knowing each, `3n − 1` by the line saying `3n − 1 ≠ 0`
    /// and N! as a positive integer.
    pub divided_by: IndexMap<usize, Vec<NotZero>>,
    /// The defined names a reason is read with written out, by the line the
    /// reason is on: a step's, a requires line's, a calculation's or a
    /// substitution's row, or the reason under a define that says a kind
    /// (`formulas::defines_read`). Each is a define the reason cites, or one
    /// a theorem of the file it cites is stated over, that the claim, a line
    /// it cites or a requires line above names, or that such a define's value
    /// names, in the order the defines are written. A define is written in
    /// terms of those above it, so a backend writing each out in turn from
    /// the last leaves none. A function's name stands for each of its
    /// applications, written out at its argument.
    pub defines_read: IndexMap<usize, Vec<String>>,
    /// Each step and requires line the checker reads at a member of its
    /// claim's "for all" (`SYNTAX.md`, a step said of every member;
    /// `citing::at_a_member`), by the line of its justification, with the
    /// binder taken off. A backend proves the body at that letter and
    /// generalises; one not here is proved whole.
    pub at_member: IndexMap<usize, AtMember>,
    /// Each "for all" a line a step may cite says that the step reads at a
    /// block's letter, with that letter, by the step's index
    /// (`Known::letters_read_at`): 5.6's "for all a ∈ {2, …, p − 2}, f(a) ∈
    /// ℤ" says f(a) ∈ ℤ at the a of the block 5.7 stands in. A backend
    /// reads the line at the letter the check read it at.
    pub read_at: Vec<Vec<ReadAt>>,
    /// What the statement's hypotheses bound below, y − 3 ≥ 0 of `y ≥ 3`
    /// (`citing::bounds`), read with the letters the header lets.
    pub statement_bounds: SaidBounds,
    /// What the lines in scope at each step bound below, by the step's
    /// index, read with the step's letters (`checker::bounds`). A backend
    /// writes a square root or a real power of a base at least 0 as a real
    /// one, as Metamath proves `√x ∈ ℝ` from `0 ≤ x`.
    pub bounds: Vec<SaidBounds>,
    /// What any line of the theorem bounds below: the statement's
    /// hypotheses, the lines in scope at every step and every requires
    /// line, a step's or a naming `let`'s, together (`statement_bounds`,
    /// `bounds`). A backend writes a square root or a
    /// real power of a base the page shows at least 0 anywhere in one form
    /// throughout, as the statement's own may come before the line that
    /// shows it.
    pub page_bounds: SaidBounds,
    /// The sets the lines in scope at each step say are finite in words,
    /// `W is finite` or `B ⊆ A` of a finite A, as printed, each with why,
    /// by the step's index (`citing::finite::finite_sets_in_words`): a
    /// count of one is a natural number from there on, as of one
    /// `said_finite` holds.
    pub finite_at: Vec<FiniteSets>,
    /// Of each "if P then Q" on the page, the sets P makes finite within Q,
    /// as `finite_sets` reads P: X of "if |X| = m then |𝒫X| = 2^m", by the
    /// whole sentence as a tree (`formulas::finite_under`). A backend that
    /// writes a count by whether its set is finite writes Q's so.
    pub finite_under: IndexMap<ByShape, FiniteSets>,
    /// The number system each letter the page's lines put in sets of
    /// numbers is in, the widest of them, A of `let A be an element` and
    /// `A ∈ ℝ ∖ ℚ` (`citing::number_sets::element_systems`): what a backend
    /// whose letters are typed gives the letter.
    pub element_systems: IndexMap<String, System>,
    /// The function letters the page's lines give a type between sets of
    /// numbers, f of `f : D → ℝ`, with the systems of the domain and the
    /// codomain (`citing::number_sets::function_systems`).
    pub function_systems: IndexMap<String, Between>,
    /// The steps that say which numbers a define's values, or a defined
    /// set's members, are among, by the define's name, in page order: `f :
    /// ℕ → ℚ`, `for all x ∈ ℚ, g(x) ∈ ℕ`, `S ⊆ ℚ` (`SYNTAX.md`, a define's
    /// numbers). The define says none itself. A backend whose numbers are
    /// typed builds the define in the widest, and takes a narrower one
    /// from the step that says it.
    pub define_values: IndexMap<String, Vec<ValuesSaid>>,
    /// The record with what the theorem's file defines outside it written
    /// out, and each phrase as its meaning, read again of the page as
    /// written (`checker::written`); None where the file defines nothing
    /// so and the record stands as read.
    pub written: Option<Box<CheckedTheorem>>,
}

/// A "for all" a cited line says, and the block's letter it is read at
/// (`CheckedTheorem::read_at`).
#[derive(Clone, Debug)]
pub struct ReadAt {
    /// The line that says the "for all", by the reference that names it.
    pub line: String,
    /// The "for all", as the line says it.
    pub said: Node,
    /// The letter of the block around the step that its set holds.
    pub letter: Node,
    /// Where the block's `let` line says the letter is in that set, `K7` of
    /// `let a ∈ {2, …, p − 2} (K7)`: what proves the letter is there.
    pub opened_by: FirstAt,
}

/// A part a reason's lines put in a number system, and how
/// (`CheckedTheorem::held_by_lines`).
#[derive(Clone, Debug)]
pub struct HeldByLines {
    pub term: Node,
    pub system: System,
    pub by: LinesHold,
}

/// How a reason's lines put a part in a number system
/// (`methods::membership::HeldHow`).
#[derive(Clone, Debug)]
pub enum LinesHold {
    /// A line states it, of a system inside the one recorded: `line` is
    /// that sentence, as the check read it.
    Stated { line: Node },
    /// An equation a line says puts it beside `other`, a term in the
    /// system (`Besides`).
    Beside(Besides),
    /// The closure table puts it there by its operation, x mod n in ℕ₀ of
    /// x ∈ ℤ and n ∈ ℕ, its parts held as the walk reads them.
    Closed,
}

/// A part a reason divides by, and why it is not zero
/// (`CheckedTheorem::divided_by`, `methods::membership::nonzero_how`).
#[derive(Clone, Debug)]
pub struct NotZero {
    pub term: Node,
    pub by: NonzeroBy,
}

/// The binder a step read at a member takes off its claim
/// (`CheckedTheorem::at_member`): "for all k ∈ X" gives letter k over X, and
/// "for all X ⊆ A" letter X over the parts of A.
#[derive(Clone, Debug)]
pub struct AtMember {
    pub letter: String,
    pub set: Node,
    /// The letter runs over the parts of `set`, `X ⊆ A`, not its members.
    pub part: bool,
}

/// Why a part a reason divides by is not zero.
#[derive(Clone, Debug)]
pub enum NonzeroBy {
    /// A line the reason rests on says so: `line` is what says it, as the
    /// check read it, `d ≠ 0` either way round or a sign, `0 < d`, `d > 0`,
    /// `d < 0` or `0 > d`; `from` is the sentence it is read from, `line`
    /// itself or a fact implying it, `d ∈ ℕ` of `d > 0`; `at` is where the
    /// page writes `from`.
    Stated {
        line: Node,
        from: Node,
        at: StatedIn,
    },
    /// Numerals alone, whose value is not zero.
    Numerals,
    /// A positive integer by what the page says once: k, j·(j + 1), 2^n
    /// and (k + 1)! where k, j and n are letters in ℕ.
    Positive,
}

/// Where the page writes a line a reason rests on (`NonzeroBy::Stated`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatedIn {
    /// A line the reason cites, by the reference that names it.
    Cited { line: String },
    /// A requires line, the step's own or one above the requires line the
    /// reason is of, by the page line it is on.
    Requires { line: usize },
    /// What a claim said of every member gives its member: x ∈ [a, b] of
    /// "for all x ∈ [a, b], …".
    Member,
}

/// A term a step puts where a notation asks a number system, and how the
/// step shows it is in that system.
#[derive(Clone, Debug)]
pub struct PlaceShown {
    pub term: Node,
    pub system: System,
    pub by: ShownBy,
}

/// The case of `inspection` that decided a claim
/// (`CheckedTheorem::inspected`, `methods::inspection::Case`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Inspection {
    /// A line of "or"s saying what a term is, one equation for each element
    /// of the set a cited membership puts it in: that membership's line, by
    /// its reference, and whether the set is a range of integers.
    OneOf { from: String, range: bool },
    /// Whether a number is prime.
    Prime,
    /// That nothing is in ∅.
    Empty,
    /// A membership of a set listed in full, or its denial.
    Member,
    /// The size of a set listed in full.
    Size,
    /// The size of a set taken by a property from a set listed in full;
    /// `kept` says of each listed member, in the list's order, whether the
    /// property holds of it.
    TakenSize { kept: Vec<bool> },
    /// A set taken by a property from a set listed in full, said equal to
    /// the members it keeps; `kept` as of `TakenSize`.
    Taken { kept: Vec<bool> },
    /// Any other the method decides.
    Other,
}

/// A step saying which numbers a define's values are among, or a defined
/// set's members (`CheckedTheorem::define_values`).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ValuesSaid {
    /// The step's index.
    pub step: usize,
    /// The numbers it says: ℕ of `for all x ∈ ℚ, g(x) ∈ ℕ`, ℚ of `f : ℕ →
    /// ℚ`.
    pub system: System,
    /// Whether the step gives the function's type, `f : ℕ → ℚ`, which a
    /// backend whose functions are typed gives the function; or says its
    /// values at every member, or a set's members, a fact of numbers that
    /// may be wider than the define's.
    pub typed: bool,
}

/// How a step shows a term is in a number system.
#[derive(Clone, Debug)]
pub enum ShownBy {
    /// By what the page says once and the lines the step names that state
    /// memberships (`methods::membership::said`).
    Said,
    /// By an equation a line the step names says, which puts the term
    /// beside `other`, a term in the system: a·f(a) of a·f(a) = f(a)·a
    /// where a requires line says f(a)·a ∈ ℤ (`Besides`).
    Beside(Besides),
    /// A function's value at a point of its domain, by its type `map`,
    /// `f : ℕ → ℕ` of f(a) with a ∈ ℕ, the function applied at `at`.
    Typed { map: Node, at: Node },
    /// The term as a define the claim cites writes it out, `value`: e(i) ∈
    /// ℕ of `let e(i) = p` with p ∈ ℕ, as p is.
    Define { value: Node },
}

/// A row of the closure table (`rules::WHOLE`) that puts a term in a
/// system by its operation, and the term's two parts in the systems the
/// row asks: (t + 1) mod 10 ∈ ℕ₀, an integer modulo a natural number.
#[derive(Clone, Debug)]
pub struct WholeRow {
    /// The row, by its operation.
    pub op: String,
    pub left: Node,
    pub right: Node,
}

/// An equation that puts a term beside `other`, a term in a number system
/// (`ShownBy::Beside`, `LinesHold::Beside`).
#[derive(Clone, Debug)]
pub struct Besides {
    /// The equation, as the lines hold it.
    pub equation: Node,
    /// Its side that is not the term.
    pub other: Node,
    /// Which side the term is: straight where it is the left side, a·f(a)
    /// of a·f(a) = f(a)·a; turned where it is the right.
    pub facing: Facing,
    /// The line stating `other` is in the system, as the lines hold it;
    /// None where the page says it once or the closure table puts it there.
    pub other_stated: Option<Node>,
    /// The closure table's row that puts `other` in the system, where no
    /// line states it: (t + 1) mod 10 beside s(t).
    pub other_row: Option<WholeRow>,
    /// Another equation the lines hold that puts `other` beside a term in
    /// the system, where no line states it, no row puts it there and the
    /// page does not say it once: y = r of `let r ∈ ℝ` and x = y = r,
    /// carrying x on from x = y.
    pub other_beside: Option<Box<Besides>>,
}

impl Besides {
    /// The record of `methods::membership`'s `Beside`.
    pub fn of(b: &crate::methods::membership::Beside) -> Besides {
        Besides {
            equation: b.equation.clone(),
            other: b.other.clone(),
            facing: match b.term_left {
                true => Facing::Straight,
                false => Facing::Turned,
            },
            other_stated: b.other_stated.cloned(),
            other_row: b.other_row.map(|(row, [left, right])| WholeRow {
                op: row.op.to_string(),
                left: left.clone(),
                right: right.clone(),
            }),
            other_beside: b.other_beside.as_deref().map(|o| Box::new(Besides::of(o))),
        }
    }
}

/// A step's citation of an item as the checker reads it (`citing::taken`,
/// or `citing::obtained` for an obtain): the group of the item's
/// conclusions it takes, and what each of the item's letters stands for.
#[derive(Clone, Debug)]
pub struct Cited {
    /// The item, by its full name.
    pub item: String,
    pub group: usize,
    /// For an obtain, the sentence that says the "there is", by its place
    /// among the sentences of all the item's groups, counted across them in
    /// order as `Concluded::sentence` is (`Taken::obtained` gives its place
    /// in its group).
    pub obtained: Option<usize>,
    pub binding: Binding,
    /// What the reading gave each letter a binder of the item holds
    /// (`Taken::bound`): for a "there is" the citation asks, or a definition
    /// folds, the witness a line names, which the build exhibits.
    pub bound: Binding,
    /// The sentences of the item's conclusions the claim takes, and which
    /// way each is read, each sentence by its place among them all, counted
    /// across the groups in order: the place of the lemma that proves it in
    /// the item's target, which names one lemma to a sentence
    /// (`targets::clauses`). None for an obtain, which takes its group's
    /// "there is" whole.
    pub concluded: Vec<Concluded>,
    /// What each reading of `concluded` is taken from, by the reading's
    /// place there, an obtain's "there is" its one: each part of what the
    /// reading asks first (`Taken::asks_first`), in order, with where it
    /// stands. Empty for a reading as written, which asks nothing first.
    pub firsts: Vec<Vec<First>>,
    /// What supplies each hypothesis of the group the citation takes, in
    /// the group's order: the fact the search took for it (`supplier`),
    /// and where that fact stands.
    pub supplied: Vec<Supplied>,
    /// Each hypothesis of the item that names a thing of a kind, with the
    /// line that introduces what stands for it (`citations::kinds_said`).
    pub kinds: Vec<KindSaid>,
    /// Each item letter the binding gives a value, with the number system
    /// the item takes it in and its value's (`citations::item_letters`).
    pub item_letters: Vec<ItemLetter>,
    /// For each of `concluded`, where the sentence read at the binding and
    /// the claim's sentence it gives are both equations, which way the one
    /// faces the other (`citations::facings`); None where either is no
    /// equation, or no side of the one is alike a side of the other.
    pub facings: Vec<Option<Facing>>,
    /// For each of `concluded`, how the sentence read at the binding met
    /// the claim's sentence it gives (`Known::alike_how`): the identity
    /// elements dropped among it, x − 0 read as x, and the parts of a
    /// notation that stand in no order taken in another order. Of the part
    /// the claim is, where it is one part of the sentence's "and"
    /// (`Concluded::part`, `within`); None where nothing of it meets the
    /// claim's sentence.
    pub meetings: Vec<Option<Meeting>>,
    /// For each of `meetings`, the two trees it is a meeting of
    /// (`MetTrees`), which its places are counted in.
    pub met_trees: Vec<Option<MetTrees>>,
    /// For each of `concluded`, where the claim's sentence is one part of
    /// what the sentence's part gives once read at the binding, a property
    /// applied taken as its body: which part of that "and", counted from 0
    /// with every conjunction taken apart (`citations::parts_within`). `P(u)` at
    /// P := S ↦ N ∈ S and for all p ∈ S, p ≤ N gives "for all p ∈ T, p ≤ N"
    /// as its part 1. None where the claim's sentence meets the part whole,
    /// or meets no part of it.
    pub within: Vec<Option<usize>>,
    /// What the citation's own pairs make the item's letters, `n := b`, as
    /// the checker reads them (`Parts::seed`): what an obtain unfolds a
    /// definition at, where it claims no conclusion of the item.
    pub written: Binding,
    /// For each of `concluded` read backwards, what the right side of its
    /// `↔` asks at the citation's values, its parts joined by "and" in
    /// order, and where each fact stands (`citations::unfolded`): `u ∈ X
    /// and P(u)` of set-builder at u := L(k), P := "there is a ∈ ℕ₀ with y
    /// = N(a)/10^a", bound a := k, is L(k) ∈ ℝ, then the witness k with k ∈
    /// ℕ₀ and L(k) = N(k)/10^k. None for a sentence read otherwise.
    pub unfolded: Vec<Option<Vec<Unfolded>>>,
    /// Each recursion the cited theorem is stated over, by its define's
    /// label, with the citing proof's define that is the same recursion,
    /// by its label: `D1` of fibonacci-natural is `D1` of a proof that
    /// defines F and G the same way (`citations::recursions_met`).
    pub recursions: IndexMap<String, String>,
}

impl Cited {
    /// The binding with what the citation's own pairs give the letters it
    /// leaves out (`written`), Z of `Z := B` where Z is named only in a
    /// map's type, as the checker finds what supplies a hypothesis
    /// (`citations::with_seed`).
    pub fn binding_with_written(&self) -> Binding {
        let mut out = self.binding.clone();
        for (letter, value) in &self.written {
            out.entry(*letter).or_insert_with(|| value.clone());
        }
        out
    }

    /// How the right side the `k`th concluded sentence reads backwards was
    /// shown (`unfolded`); None for a sentence read otherwise.
    pub fn unfolding(&self, k: usize) -> Option<Unfolding> {
        let parts = self.unfolded.get(k)?.as_ref()?;
        let stated = parts.iter().all(|p| matches!(p, Unfolded::Fact { .. }))
            && parts.iter().any(|p| {
                matches!(
                    p,
                    Unfolded::Fact { fact, by: SuppliedBy::Line(_), .. }
                        if matches!(fact.notation(), THERE_IS | THERE_IS_SOME)
                )
            });
        Some(match parts.as_slice() {
            _ if stated => Unfolding::Stated,
            [Unfolded::Witness { .. }] => Unfolding::Witnessed,
            _ => Unfolding::Parts,
        })
    }
}

/// The two trees a concluded sentence's meeting is of (`Cited::meetings`),
/// each before its standard form, in which the meeting's places are
/// counted (`matching::standard`, `Meeting::with_identities_dropped`).
#[derive(Clone, Debug)]
pub struct MetTrees {
    /// What the item gives at the citation's values, as the checker
    /// compared it: its sentence read the recorded way, or the part of it
    /// that met; the first tree.
    pub item: Node,
    /// The claim's part, as the checker read it, with the defines the step
    /// cites read out; the second tree.
    pub claim: Node,
}

/// How a definition's right side read backwards was shown, as the checker
/// unfolded it (`Cited::unfolding`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unfolding {
    /// Its "there is" a cited line states whole, with no witness shown: the
    /// line says what the right side asks.
    Stated,
    /// It is one "there is", shown at the witness the citation gives it.
    Witnessed,
    /// Its parts, each where the checker found it supplied.
    Parts,
}

/// One part of what a definition's right side asks, at a citation's values
/// (`Cited::unfolded`).
#[derive(Clone, Debug)]
pub enum Unfolded {
    /// A fact, what supplies it, and how the fact the supplier states met
    /// it (`Supplied::meeting`): `|a(n)| < ε` on a line for `|a(n) − 0| <
    /// ε`, the identity element dropped. None where no line writes it.
    Fact {
        fact: Node,
        by: SuppliedBy,
        meeting: Option<Meeting>,
    },
    /// A "there is": the witness the citation gives its letter, that the
    /// witness is in the letter's domain, and the parts of its body at the
    /// witness.
    Witness {
        value: Node,
        member: Box<Unfolded>,
        body: Vec<Unfolded>,
    },
}

/// Which way an item's equation, read at a citation's values, faces the
/// claim's: `P(j+1) = P(j)·h(j+1)` faces `P(j)·h(j+1) = P(j+1)` turned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Facing {
    /// A side of the one is alike the same side of the other.
    Straight,
    /// A side of the one is alike the other side of the other, and neither
    /// is alike its own.
    Turned,
}

/// A contradiction's supposition as the checker relates it to what the
/// block or part is to show.
#[derive(Clone, Debug)]
pub struct Supposition {
    pub shape: Supposed,
    /// What the supposition is set against: the block's claim, or what the
    /// part owes, with the block's `let` and `assume` lines taken off it.
    pub against: Node,
    /// How what the one denies meets the other (`Known::alike_how`).
    pub meeting: Meeting,
}

/// How a contradiction's supposition stands to what the block or part is
/// to show, the two shapes `METHODS.md` gives `contradiction`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Supposed {
    /// The supposition is the claim negated: the claim is shown by
    /// reductio.
    ClaimDenied,
    /// The claim is the supposition negated: a negation is shown directly.
    Denial,
}

/// The two lines a step written `contradicting N` closes its block or case
/// on.
#[derive(Clone, Debug)]
pub struct Contradicted {
    /// What of line N the step's claim opposes, and where it stands in the
    /// line: a sentence of it, a part of one, the sentences together, or a
    /// "for all" of it read at a block's letter.
    pub at: FirstAt,
    /// Which of the two says the other negated.
    pub negated: Negating,
    /// How what the negating one denies meets the other
    /// (`Known::alike_how`).
    pub meeting: Meeting,
}

/// The line a `cases` step splits, the first it cites that is not a
/// define, and how its cases' assumptions joined by "or" meet it
/// (`formulas::cases_splits`): `cases, from H9` of H9 "H = C or H ≠ C".
#[derive(Clone, Debug)]
pub struct CasesSplit {
    /// What of the line the cases split: its one sentence, its sentences
    /// together, or its sentence read at a block's letter.
    pub at: FirstAt,
    /// How the cases' assumptions joined by "or", the first tree, meet it
    /// (`Known::alike_how`): an equation or an order either way round.
    pub meeting: Meeting,
    /// Whether they meet the line only with the defines it cites written
    /// out (`Said::cited`), and not as the page writes it.
    pub read_out: bool,
}

/// Of a step and the line it contradicts, the one that says the other
/// negated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Negating {
    /// The step's claim is the line negated: `a ≠ 0` against `a = 0`.
    Step,
    /// The line is the step's claim negated.
    Line,
}

/// Where a step citing a define of a name or a function has the define in
/// its equation (`CheckedTheorem::define_sides`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefineSide {
    /// The left side is the name, applied or not, and the right is its
    /// value.
    Left,
    /// The right side is the name, applied or not.
    Right,
    /// Neither side is the name at its head; it stands inside a side, as p
    /// does in ∫(0 to 1) p(t) dt, and the equation is read where it stands.
    Inside,
}

/// The two ends of a `substitute` step's rows as the checker met them
/// (`CheckedTheorem::substitute_ends`).
#[derive(Clone, Debug)]
pub struct RowEnds {
    /// Where in the line the first row cites that row stands; None where
    /// the line's sentences say it only together.
    pub first: Option<FirstAt>,
    /// How the last row meets the claim (`Known::alike_how`).
    pub last: Meeting,
    /// Whether the last row writes the claim in its other form
    /// (`rules::OTHER_FORMS`) and meets the claim only so.
    pub last_other_form: bool,
}

/// A line a citation names that states a fact its reading is taken from.
#[derive(Clone, Debug)]
pub struct FirstAt {
    /// The line, by the reference that names it.
    pub line: String,
    /// The sentence of the line that states the fact, or a part of which
    /// does, by its place among the sentences the line writes, from 0; past
    /// them, a "for all" of the line read at a block's letter, in the order
    /// the line writes them. None where the fact is the line's sentences
    /// together.
    pub sentence: Option<usize>,
    /// Where the fact is one part of the sentence's conjunction, which part,
    /// counted from 0 left to right with every conjunction taken apart
    /// (`citing::conjuncts`).
    pub part: Option<usize>,
    /// The fact as the page writes it, with its defines kept: what a
    /// backend that names the line's sentences its own way finds it by.
    pub written: Node,
    /// Where the line does not write the fact but implies it, the rule:
    /// the sentence or part named above says what implies it, `k ∈ {1, …,
    /// n}` of `k ≤ n`.
    pub implied: Option<Implication>,
    /// Where the fact is the equation between two terms of a chain the
    /// sentence writes, x = w of x = y = z = w, which two: a backend proves
    /// it by joining the chain's links between them.
    pub pair: Option<ChainTerms>,
}

/// Two terms of a chain of equations, by their places among its terms from
/// 0, the first before the second (`FirstAt::pair`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChainTerms {
    pub from: usize,
    pub to: usize,
}

/// A part of the body of a line's "for all", joined by "and"
/// (`Restated::UnderClaim`): s(x) ∈ ℕ₀, the first of two, of
/// "for all x ∈ ℚ, s(x) ∈ ℕ₀ and numer(x) = …".
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BodyPart {
    /// Its place among the parts, from 0.
    pub part: usize,
    /// How many parts the body has.
    pub of: usize,
}

/// An application of a function a define lets on a domain, in a step of a
/// method citing the define, and what says its argument is in the domain
/// (`CheckedTheorem::applied_domains`).
#[derive(Clone, Debug)]
pub struct AppliedDomain {
    /// The define's label, D1.
    pub label: String,
    /// The argument, a of q(a).
    pub arg: Node,
    pub said: DomainSaid,
}

/// What says a define's argument is in the define's domain
/// (`CheckedTheorem::define_domains`).
#[derive(Clone, Debug)]
pub enum DomainSaid {
    /// A line says it: one the step cites, or else the `let` line that
    /// introduces the argument.
    Line(FirstAt),
    /// The claim is said of every member of a set inside the domain, and the
    /// argument is the member: `for all j ∈ {1, …, m}` over a define on ℕ.
    Member,
    /// The argument is the index of a sum in the claim, and the range the
    /// sum runs over lies inside the domain: k of Σ(k = 1 to n) t(k) over a
    /// define on ℕ.
    SumRange,
    /// The argument is the index of a sequence's limit in a line the step
    /// cites, which runs over ℕ, and the domain holds ℕ: n of `S(n) → K as
    /// n → ∞` over a define on ℕ.
    LimitIndex,
}

impl FirstAt {
    /// Whether the two name one place: the line, sentence and part.
    pub fn same_place(&self, other: &FirstAt) -> bool {
        self.line == other.line
            && self.sentence == other.sentence
            && self.part == other.part
    }
}

/// One part of what an obtain step claims after its memberships, and the
/// part of the "there is" it obtains from that the part is
/// (`citations::check_obtained_claims`).
#[derive(Clone, Debug)]
pub struct ObtainedPart {
    /// The claim's sentence, by its place among the step's sentences.
    pub sentence: usize,
    /// The part of that sentence, joined by "and", counted from 0
    /// (`citing::conjuncts`).
    pub part: usize,
    /// The part of the "there is"'s body it is, counted alike.
    pub owed: usize,
    /// That part as the checker read it, with each letter obtained put in
    /// for the one the "there is" binds: what a backend finds among the
    /// body's parts.
    pub owed_written: Node,
    /// How the two meet (`Known::alike_how`).
    pub meeting: Meeting,
}

/// A `transitivity` step's chain (`CheckedTheorem::links`): its links in
/// the order cited, and whether the claim writes the chain the other way
/// round, `c = a` of `a = b = c`.
#[derive(Clone, Debug)]
pub struct Chain {
    pub links: Vec<ChainLink>,
    pub claim_turned: bool,
    /// Whether each link's right side is the next one's left side, and the
    /// chain's ends the claim's sides, as the page writes them; not where
    /// the checker met them only with identity elements dropped, `n·1`
    /// beside `n`.
    pub as_written: bool,
    /// Whether the chain goes down as the lines are cited, an order link of
    /// it `≥` or `>` as the chain reads it, so that a writer that builds an
    /// order low side first folds the links from the last.
    pub falls: bool,
    /// How the chain's first term meets the claim's first, and its last the
    /// claim's last (`Known::alike_how`), the claim read as `claim_turned`
    /// says.
    pub ends: ChainEnds,
}

/// How a chain's ends meet the claim's (`Chain::ends`).
#[derive(Clone, Debug, Default)]
pub struct ChainEnds {
    pub first: Meeting,
    pub last: Meeting,
}

/// One link of a `transitivity` step's chain (`CheckedTheorem::links`).
#[derive(Clone, Debug)]
pub struct ChainLink {
    /// The relation the cited line gives the chain, as the line writes it.
    pub said: Node,
    /// Where it stands: a sentence of the line or a part of one, or the
    /// equation of a define the step cites. None where the checker finds
    /// it in neither.
    pub at: Option<OrderFact>,
    /// Whether the chain reads it from its right side: `b = a` as `a = b`,
    /// `b > a` as `a < b`.
    pub turned: bool,
    /// How the chain's term before this link, the previous link's right
    /// side as the chain reads it, meets this link's left side
    /// (`Known::alike_how`): as written for the first link, and where the
    /// two are written alike. A middle term the page writes two ways, |AB|
    /// and |BA|, meets by a flip.
    pub joint: Meeting,
    /// Where the link cites a define of a name, which way `said` faces the
    /// define's equation (`formulas::define_named_facing`); None where no
    /// side meets or the link cites no such define.
    pub define_facing: Option<Facing>,
}

/// What an order step rests on, by sentence of its claim
/// (`CheckedTheorem::orders`): for each sentence, each of its parts joined
/// by "and", in order.
#[derive(Clone, Debug)]
pub struct OrderStep {
    pub sentences: Vec<Vec<OrderPart>>,
}

/// What one part of an order step's claim rests on (`OrderStep`).
#[derive(Clone, Debug)]
pub struct OrderPart {
    /// The facts the method adds to reach it, in order: for a plain step,
    /// the combination the checker found
    /// (`methods::inequalities::combined`), then the equation of each
    /// define the step cites, which it reads written out; for rows, or a
    /// requires line naming one manipulation, the line the first row or the
    /// manipulation starts from.
    pub uses: Vec<OrderFact>,
    /// The disequalities the combination takes both ways, below and above.
    pub split: Vec<OrderFact>,
    /// Where the part is a disequality a fact says, that fact.
    pub restates: Option<OrderRestated>,
    /// Where the part is a disequality a `weakening` row or manipulation
    /// makes of an order, which way the order runs.
    pub weakened: Option<Weakened>,
}

/// A disequality a fact says (`OrderPart::restates`).
#[derive(Clone, Debug)]
pub struct OrderRestated {
    pub by: OrderFact,
    /// Whether the fact says it the other way round, `b ≠ a` of `a ≠ b`.
    pub turned: bool,
}

/// The order a `weakening` makes a disequality of, read from the
/// disequality's left side (`OrderPart::weakened`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Weakened {
    /// `a < b`, for `a ≠ b`.
    Below,
    /// `a > b`, for `a ≠ b`.
    Above,
}

/// Where a fact an order step adds stands (`OrderPart`).
#[derive(Clone, Debug)]
pub enum OrderFact {
    /// A line the step cites: a sentence, a part of one, or what one
    /// implies, `k ≥ 1` of `k ∈ ℕ`.
    Line(FirstAt),
    /// A define the step cites, its equation.
    Define(String),
    /// What the kind a define the step cites says its name is implies,
    /// `n ≥ 1` of `let n = gcd(t, w), a positive integer`: the define's
    /// label, the rule, and the fact as the page writes it.
    Kind {
        define: String,
        implied: Implication,
        written: Node,
    },
    /// One of the step's own requires lines above the one the fact is
    /// for, by its place among them, counted from 0, or what it implies.
    Requires {
        line: usize,
        implied: Option<Implication>,
    },
    /// What the member a claim said of every member is read at implies,
    /// `i ≥ 1` of `i ∈ ℕ`: the rule, and the fact as the page writes it.
    Member { implied: Implication, written: Node },
}

/// A run of a `join` step's claim's parts that one line it cites states as
/// one fact (`CheckedTheorem::joined_wholes`): `a > 0 and b > 0` of the
/// claim `a > 0 and b > 0 and c > 0`, from a line saying it whole.
#[derive(Clone, Debug)]
pub struct JoinedWhole {
    /// The run's first part, by its place among the claim's parts, counted
    /// from 0 across its sentences (`citing::conjuncts`).
    pub first: usize,
    /// How many parts the run holds, more than one.
    pub count: usize,
    /// Where the line states the run.
    pub at: FirstAt,
    /// How the line met the run (`JoinedPart::meeting`).
    pub meeting: Option<Meeting>,
}

/// One part of a `join` step's claim and where it stands
/// (`CheckedTheorem::joined`).
#[derive(Clone, Debug)]
pub struct JoinedPart {
    pub at: FirstAt,
    /// How the line met the part as the page writes it (`Known::alike_how`),
    /// a define the step cites read out where the two differ
    /// (`Meeting::unfolded`), as `Supplied::meeting` records it for a
    /// hypothesis.
    pub meeting: Option<Meeting>,
}

/// How an `antisymmetry` step's two lines make its equation
/// (`CheckedTheorem::antisymmetric`): `below` says the claim's left side is
/// at most its right, `above` the converse, each as its line writes it.
#[derive(Clone, Debug)]
pub struct Antisymmetric {
    pub below: FirstAt,
    pub above: FirstAt,
}

/// How an `instantiate` step's instance of the line it names reaches its
/// claim (`citations::check_instance_claimed`).
#[derive(Clone, Debug)]
pub struct Instantiated {
    /// The sentence of the line, or the part of one, instantiated.
    pub at: FirstAt,
    /// The conditions of the instance, `if A then`, taken off on the way to
    /// the claim, outermost first, each with where the line the step names
    /// that meets it stands.
    pub conditions: Vec<Condition>,
    /// How what is left meets the claim (`Known::alike_how`).
    pub meeting: Meeting,
    /// Each value the step puts in a domain, in the order the line binds
    /// their letters, with where its membership of the domain stands
    /// (`citations::value_guards`).
    pub guards: Vec<Guard>,
    /// The letter of the line the values leave open that the step reads at
    /// its claim's own letter (`citations::open_at_claim`): k of "for all N,
    /// for all k ∈ {1, …, N}, P" at N := n, in a claim "for all k ∈ {1, …,
    /// n}". Such a step is read at a member (`CheckedTheorem::at_member`).
    pub at_claim: Option<AtClaim>,
}

/// A letter an instantiation leaves open, read at the claim's own
/// (`Instantiated::at_claim`).
#[derive(Clone, Debug)]
pub struct AtClaim {
    /// The letter of the line, as the page writes it, as a guard names it.
    pub letter: String,
    /// The letter of the claim's "for all", which the step gives it.
    pub claim: Node,
}

/// A condition of an instance an instantiation takes off: `for all s ∈ S,
/// s ≤ U(k)` of "if u is an upper bound of S then c ≤ u" at u := U(k), and
/// what supplies it.
#[derive(Clone, Debug)]
pub struct Condition {
    /// The condition at the values, as compared, defined names written out.
    pub read: Node,
    pub by: SuppliedBy,
}

/// A value an instantiation puts in a domain: `f(a) ∈ {2, …, p − 2}` of
/// `a := f(a)` in "for all a ∈ {2, …, p − 2}", and what supplies it.
#[derive(Clone, Debug)]
pub struct Guard {
    /// The letter of the line the value is given to.
    pub letter: String,
    /// The membership as the page writes it, at the value as written.
    pub written: Node,
    pub by: SuppliedBy,
}

/// Where a substitution puts its equation, and what at (`Substituted`).
#[derive(Clone, Debug)]
pub enum SubstitutedInto {
    /// A fact of the line the step names, where it stands there.
    Line(FirstAt),
    /// A side of the claim `t = t′`, by its place, 0 or 1: the side the
    /// equation is put into makes the other.
    ClaimSide(usize),
    /// The row above, of a `substitute` step's rows: the row's change, as
    /// its reason proves it, put into the row before it makes the row
    /// (`CheckedTheorem::substituted_rows`).
    RowAbove,
    /// Something the line says that no sentence or part of it states, a
    /// part of a "for all" read at a block's letter or a set's members;
    /// `Substituted::start` is what it says.
    Unplaced,
}

/// How a `substitute` step or calculation row makes its claim: the
/// equation it puts in, which way round, and the places of what it is put
/// into that it is put at (`citations::substitutions`).
#[derive(Clone, Debug)]
pub struct Substituted {
    /// The equation, as the page writes it: the step's own, or the one the
    /// line it is taken from says.
    pub equation: Node,
    /// Where the equation stands in the line it is taken from; None where
    /// the step writes it from a define or from arithmetic, or the line
    /// says it as a whole.
    pub from: Option<FirstAt>,
    /// What the equation is put into (`SubstitutedInto`).
    pub into: SubstitutedInto,
    /// What it is put into, as the page writes it.
    pub start: Node,
    /// Where it is put (`matching::substitution_places`): which way round,
    /// and each place by its path of children from the top of `start`.
    pub put: SubstitutionPlaces,
    /// How what the putting makes meets the claim (`Known::alike_how`): as
    /// written; with identity elements the putting makes and the claim
    /// leaves out, `1·x` written `x`; or turned round, `b ≡ c` of the claim
    /// `c ≡ b`, or a listed set's members in another order.
    pub meeting: Meeting,
    /// Whether what the putting makes is the claim's other form
    /// (`rules::OTHER_FORMS`), `Q is not on line HK` for `Q ∉ line HK`,
    /// which a backend carries back to the claim, and not the claim itself.
    pub made_other_form: bool,
    /// Where a place writes the side put for with the parts of a notation
    /// that stands in no order in another order, |BA| for the side |AB|
    /// (`matching::places_alike`): each such flip, the side's term first
    /// (`Known::alike_how` of the side and the place). Empty where every
    /// place is written as the side is.
    pub place_flips: Vec<Flip>,
    /// Where the step writes its equation with the parts of a notation that
    /// stands in no order in another order than the line it is taken from
    /// says it, `|AC| = 4` of a line `|CA| = 4`: each such flip, the step's
    /// equation's term first (`Known::alike_how` of the equation and the
    /// line). Empty where the two are written alike, or no line gives it.
    pub equation_flips: Vec<Flip>,
    /// Of an equation a define gives, which way the step writes it beside
    /// the define's own, name or function applied on the left: straight
    /// for `q(a) = a + 1`, turned for `a + 1 = q(a)`. None of an equation
    /// from a line or from arithmetic.
    pub define_facing: Option<Facing>,
    /// Of an equation a line gives (`from`), which way the line writes it
    /// beside `equation`: turned where the step writes `b = a` of the
    /// line's `a = b`. None where no line gives it.
    pub line_facing: Option<Facing>,
}

/// One letter of a cited item the citation gives a value, with the number
/// systems the page puts the two in (`Cited::item_letters`): for
/// `mun:abs-nonneg x := C` with C real, x is taken in ℂ by the item's
/// `x ∈ ℂ`, and C is in ℝ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemLetter {
    /// The item's letter, as the binding names it.
    pub letter: Symbol,
    /// The number system the item takes it in, by its own hypothesis
    /// `x ∈ S`; None where it asks it in none.
    pub item_system: Option<System>,
    /// The narrowest number system the page says its value is in once;
    /// None for a value in none, a set or a function.
    pub value_system: Option<System>,
    /// For a letter that stands for a set, the number system its value is
    /// as a set, ℕ of `X := ℕ`; None for any other value.
    pub value_set: Option<System>,
}

/// What one sentence of an exhibit's claim shows, a "there is".
#[derive(Clone, Debug)]
pub struct Exhibit {
    /// What each letter of the "there is" stands for.
    pub values: Binding,
    /// Each fact the "there is" asks of its values, in order: each letter
    /// in its domain, then each part of its body joined by "and"
    /// (`citing::conjuncts`), with where it stands, as a citation's
    /// hypotheses are placed.
    pub shown: Vec<Supplied>,
}

/// One part of what a reading of a cited item asks first, the definition's
/// side it is unfolded from (`Cited::firsts`): where it stands, found as a
/// hypothesis the citation needs is (`Cited::supplied`), the cited line,
/// the sentence of it, a requires line or the `let` line that says a
/// membership once, or `Unstated` where nothing does, a part the
/// citation's values make true.
#[derive(Clone, Debug)]
pub struct First {
    /// The part as the item writes it, at the citation's values: the tree
    /// `meeting` counts its first places in.
    pub asked: Node,
    pub by: SuppliedBy,
    /// How the line met the part at the citation's values
    /// (`Known::alike_how`), as `Supplied::meeting` records it for a
    /// hypothesis: the part's own parts in another order, the sides turned,
    /// identity elements dropped. None where no line writes it.
    pub meeting: Option<Meeting>,
}

/// A hypothesis of a cited item that names a thing of a kind the page never
/// states of it, `let A be a set`, `let G be a group with …`
/// (`Library::kind_lines`; `Cited::kinds`), and where the citing proof
/// says what stands for it is one.
#[derive(Clone, Debug)]
pub struct KindSaid {
    pub at: HypothesisAt,
    /// The item's letter for the thing.
    pub letter: String,
    /// The line in scope that introduces the citation's value for the
    /// letter, by its label: a `let` of the header or of a block around the
    /// step, or an `obtain` above it. None where the value is no letter so
    /// introduced, ℝ or sup S, whose kind its own shape gives.
    pub line: Option<String>,
}

/// What supplies one hypothesis of a cited item (`Cited::supplied`).
#[derive(Clone, Debug)]
pub struct Supplied {
    /// The hypothesis as the item's group asks it, in the item's letters.
    pub want: Node,
    pub by: SuppliedBy,
    /// Where the item writes the hypothesis, by which a backend that
    /// states the item finds it among its own; None for a fact that is no
    /// item's hypothesis, a value's domain or an exhibit's.
    pub at: Option<HypothesisAt>,
    /// How the fact the line writes met the hypothesis at the citation's
    /// values (`Known::alike_how`), as `Cited::meetings` records it for a
    /// conclusion: a listed set's members in another order, the identity
    /// elements dropped, the two sides turned. None where no line writes
    /// it.
    pub meeting: Option<Meeting>,
    /// Where the line says a "for all" over a set the hypothesis asks of a
    /// set inside it (`SYNTAX.md`; `citing::supply::narrowed`): "for all k ∈
    /// ℕ" for "for all k ∈ {1, …, n}". None where the two are over one set.
    pub narrowed: Option<Narrowed>,
    /// Of a "there is" no line states whole, each letter it binds, outermost
    /// first, with the value the search gave it (`Cited::bound`) and where
    /// that value's membership of the letter's domain stands: `by` then
    /// says where the body stands at those values, a line that states it
    /// (`citations::witnessed_at`) or none, where the body says what goes
    /// without saying. Empty where a line states the "there is" whole, and
    /// for any other hypothesis.
    pub witnesses: Vec<WitnessIn>,
}

/// A value a "there is" hypothesis is supplied at
/// (`Supplied::witnesses`): k′ := m·(2m + 1) of "there is k′ ∈ ℤ with
/// 3·k·(k + 1) = 6·k′", with where m·(2m + 1) ∈ ℤ stands.
#[derive(Clone, Debug)]
pub struct WitnessIn {
    /// The item's letter.
    pub letter: String,
    pub value: Node,
    /// The value's membership of the letter's domain at the citation's
    /// values, in the standard order.
    pub said: Node,
    /// Where that membership stands.
    pub member: SuppliedBy,
}

/// A part a said-once walk takes from a line (`OnceReason::Stated`) and
/// where it stands (`SaidOnceFact::stated`): a(n) in ℝ of `a(n) + 1 ∈ ℝ`,
/// through the type line `a : ℕ → ℝ` and n's `let`.
#[derive(Clone, Debug)]
pub struct StatedAt {
    pub term: Node,
    pub system: System,
    /// Where the part's membership stands, found as a hypothesis's is
    /// (`Suppliers::placed`), never by the walk itself.
    pub by: SuppliedBy,
}

/// A "for all" a line says over one set and a hypothesis asks over a set
/// inside it (`Supplied::narrowed`), by the row of `rules::RANGE_WITHIN`
/// or `rules::WITHIN` that puts the one inside the other.
#[derive(Clone, Debug)]
pub struct Narrowed {
    /// The line's set, ℕ.
    pub from: Node,
    /// The set the hypothesis asks, {1, …, n}.
    pub to: Node,
}

/// How the lines a `restate` step or a requires line names give its fact
/// (`CheckedTheorem::restated`).
#[derive(Clone, Debug)]
pub enum Restated {
    /// A line states it, a "for all" read at a block's letter or what a line
    /// implies among them, `k ≥ 1: from K` of K saying `k ∈ ℕ`; with how the
    /// line met it where not as written: turned, identity elements dropped,
    /// bound letters renamed, `d = n` of `n = d·1`.
    Stated {
        at: FirstAt,
        meeting: Option<Meeting>,
    },
    /// A requires line a line states under the claim's leading "for all",
    /// not alone: `g′(x) ≠ 0: from H11` of a claim "for all x ∈ D" and H11
    /// "for all x ∈ D, g′(x) ≠ 0"; with how the line met it, and the part of
    /// the line's own "for all" body the fact is, where it is one part of
    /// several.
    UnderClaim {
        at: FirstAt,
        meeting: Option<Meeting>,
        part: Option<BodyPart>,
    },
    /// A requires line saying "for all" over a set inside the one a line
    /// says it over, `for all k ∈ {1, …, n}, F(k) ∈ ℝ` from `for all k ∈ ℕ,
    /// F(k) ∈ ℝ`: where the line says it, and the two sets.
    Narrowed { at: FirstAt, narrowed: Narrowed },
    /// A requires line no one line states, given by what the lines give
    /// together (`SuppliedBy`): a function's value in its codomain from its
    /// type and its argument's membership, each on its line
    /// (`SuppliedBy::Through`), or a membership said once.
    Lines(SuppliedBy),
}

impl Restated {
    /// Where the one line that gives the fact says it; None where the lines
    /// give it together.
    pub fn at(&self) -> Option<&FirstAt> {
        match self {
            Restated::Stated { at, .. }
            | Restated::UnderClaim { at, .. }
            | Restated::Narrowed { at, .. } => Some(at),
            Restated::Lines(_) => None,
        }
    }

    /// How the line met the claim, where the record says.
    pub fn meeting(&self) -> Option<&Meeting> {
        match self {
            Restated::Stated { meeting, .. } | Restated::UnderClaim { meeting, .. } => {
                meeting.as_ref()
            }
            Restated::Narrowed { .. } | Restated::Lines(_) => None,
        }
    }

    /// `at`, to rewrite.
    pub fn at_mut(&mut self) -> Option<&mut FirstAt> {
        match self {
            Restated::Stated { at, .. }
            | Restated::UnderClaim { at, .. }
            | Restated::Narrowed { at, .. } => Some(at),
            Restated::Lines(_) => None,
        }
    }
}

/// Where the fact a hypothesis is supplied by stands.
#[derive(Clone, Debug)]
pub enum SuppliedBy {
    /// A line the citation names, a sentence of it, or a part of one.
    Line(FirstAt),
    /// One of the step's own `requires` lines.
    Requires {
        /// The line, by its place among the step's, counted from 0.
        line: usize,
        /// Where the line does not write the fact but implies it, the rule.
        implied: Option<Implication>,
    },
    /// A `let` line in scope the step does not name: a membership said once
    /// where the letter is let, or what that membership implies.
    SaidOnce(FirstAt),
    /// No line: a membership the page says once of a term no `let` line
    /// writes, `k + 1 ∈ ℕ₀` of a k in ℕ₀, for the reason the said-once walk
    /// gives.
    Walked(SaidOnceFact),
    /// No one line: a membership a function's type or a subset carries,
    /// `f(x) ∈ Y` of `f : X → Y` and `x ∈ X` (`citing::function_values`),
    /// `k ∈ B` of `A ⊆ B` and `k ∈ A`: where each of the two stands.
    Through {
        /// The function's type, or the subset.
        carrier: Box<SuppliedBy>,
        /// The membership of the argument, or of the smaller set.
        member: Box<SuppliedBy>,
    },
    /// No line: the membership a step's claim "for all t ∈ A, …" gives the
    /// step that proves it in one line (`citing::claimed_member`), by the
    /// letter as the page writes it.
    Bound { letter: String },
    /// No line: an equation whose two sides are one once the citation's
    /// values are put in, `P = 1·P` (`SYNTAX.md`, an identity element goes
    /// without saying), with how the two met (`Known::alike_how`).
    Identity(Meeting),
    /// No one line: an "and" no one line says, each part placed as a fact
    /// is, in the order the "and" joins them (`citing::conjuncts`).
    Parts(Vec<SuppliedBy>),
    /// No line: a fact the citation's values make true.
    Unstated,
}

/// Whether `step` owns a block: it opens one with a line above its steps,
/// or it has parts.
fn owns_block(step: &Step) -> bool {
    !step.openers.is_empty() || !step.parts.is_empty()
}

impl CheckedTheorem {
    /// The shape of `thm`'s proof. A step stands in the innermost block
    /// whose owner's number is a proper prefix of its own, in the part its
    /// parse gives it; a number written out of its block is
    /// `check_numbering`'s to report, and here stands in the outermost block
    /// it still fits.
    pub fn of(thm: &Theorem) -> CheckedTheorem {
        let mut out = CheckedTheorem::default();
        let mut open: Vec<usize> = Vec::new();
        for (i, step) in thm.steps.iter().enumerate() {
            while let Some(&b) = open.last() {
                let owner = &thm.steps[out.blocks[b].owner].number;
                if step.number.depth() > owner.depth()
                    && step.number.prefix(owner.depth()) == *owner
                {
                    break;
                }
                open.pop();
            }
            let place = open.last().map(|&b| Place {
                block: b,
                part: step.part,
            });
            if let Some(p) = place {
                out.blocks[p.block].children.push(i);
            }
            out.places.push(place);
            if owns_block(step) {
                out.blocks.push(Block {
                    owner: i,
                    within: place,
                    children: Vec::new(),
                    owes: Vec::new(),
                });
                open.push(out.blocks.len() - 1);
            }
        }
        for d in &thm.defines {
            let next = thm.steps.iter().position(|s| s.line > d.line);
            out.defines.push(next.and_then(|i| out.places[i]));
        }
        out
    }

    /// The index of `step` among `thm`'s steps. A requires line read as a
    /// step (`requires_as_step`) stands where its step does, and so does the
    /// reason of a chain's line or a row (`chain_reasons`).
    pub fn index_of(thm: &Theorem, step: &Step) -> Option<usize> {
        thm.steps
            .iter()
            .position(|s| s.line == step.line)
            .or_else(|| {
                thm.steps.iter().position(|s| {
                    s.requires.iter().any(|r| r.line == step.line)
                        || s.just.chain.iter().any(|(_, no)| *no == step.line)
                        || s.just.rows.iter().any(|(_, no)| *no == step.line)
                })
            })
    }

    /// The block the step at `owner` opens, where it opens one.
    pub fn block_of(&self, owner: usize) -> Option<&Block> {
        self.blocks.iter().find(|b| b.owner == owner)
    }

    /// Every place the step at `at` stands in, innermost first: its own
    /// place, the place its block's owner stands in, and so out.
    pub fn around(&self, at: usize) -> Vec<Place> {
        let mut out = Vec::new();
        let mut here = self.places.get(at).copied().flatten();
        while let Some(p) = here {
            out.push(p);
            here = self.blocks[p.block].within;
        }
        out
    }

    /// Whether what stands at `place` is in scope at the step at `at`: what
    /// stands at the outermost level is everywhere; what stands in a block
    /// is inside that block only, and in a block with parts inside its own
    /// part only.
    pub fn encloses(&self, place: Option<Place>, at: usize) -> bool {
        let Some(p) = place else { return true };
        self.around(at)
            .iter()
            .any(|a| a.block == p.block && (p.part.is_none() || a.part == p.part))
    }

    /// Whether the define at `index` among the theorem's defines is in scope
    /// at `step`: written above it, in a place that encloses it.
    pub fn define_in_scope(&self, thm: &Theorem, index: usize, step: &Step) -> bool {
        let Some(d) = thm.defines.get(index) else {
            return false;
        };
        if d.line >= step.line {
            return false;
        }
        match Self::index_of(thm, step) {
            Some(at) => self.encloses(self.defines.get(index).copied().flatten(), at),
            None => true,
        }
    }

    /// The step at `number` written nearest above `step`.
    pub fn written(thm: &Theorem, number: &StepPlace, step: &Step) -> Option<usize> {
        thm.steps
            .iter()
            .rposition(|s| &s.number == number && s.line < step.line)
    }
}

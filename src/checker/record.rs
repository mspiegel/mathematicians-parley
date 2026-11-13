//! What the checker decides about a theorem, once, for itself and for the
//! build: the block each step stands in and which part of it, each block's
//! steps and its last, the place each define is written in, the sort of
//! each name, the functions typed at each step, and the problems it finds.
//!
//! The build is handed this rather than working it out again as it walks
//! the proof, so the two cannot read one proof two ways.

use std::sync::Arc;

use indexmap::IndexMap;

use crate::citing::{Concluded, Group};
use crate::corpus::{Step, StepPlace, Theorem};
use crate::formula::page::Sentence;
use crate::formula::{Node, Sorts};
use crate::matching::{Binding, Definitions};
use crate::outcome::{Checked, Problem};
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
    read: rustc_hash::FxHashMap<PartKey, Node>,
}

impl PageReading {
    pub fn new(read: rustc_hash::FxHashMap<PartKey, Node>) -> PageReading {
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
    read: rustc_hash::FxHashMap<ItemKey, Checked<Node>>,
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
    pub function_types: IndexMap<String, Vec<crate::citing::Want>>,
    /// What each group of each item says of its terms, its phrases written
    /// out, by the item's full name and the group's place
    /// (`checker::written::item_facts`).
    pub item_facts: IndexMap<String, Vec<GroupFacts>>,
}

/// What one group of an item says of its terms, read as a theorem's lines
/// are (`LibraryReading::item_facts`).
#[derive(Clone, Debug)]
pub struct GroupFacts {
    /// What its hypotheses bound below (`citing::bounds`).
    pub bounds: crate::citing::bounds::SaidBounds,
    /// The sets its hypotheses make finite (`citing::finite::said_finite`).
    pub finite: crate::citing::finite::SaidFinite,
    /// For each sentence it concludes, the number system each set letter of
    /// numbers holds by the hypotheses and that sentence
    /// (`citing::number_sets::set_letter_systems`).
    pub set_systems: Vec<IndexMap<String, crate::rules::System>>,
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
    /// How the case's value meets the claim's other side (`Known::alike_how`):
    /// as it stands, or with arithmetic left; None where they met only as
    /// `Known::alike` reads them.
    pub meeting: Option<crate::matching::Meeting>,
}

/// A theorem as the checker reads it.
#[derive(Clone, Debug, Default)]
pub struct CheckedTheorem {
    /// Every formula on the page, read.
    pub page: PageReading,
    /// Every sentence of every item the corpus may cite, read: one reading
    /// for the corpus, shared by each theorem's record.
    pub items: std::sync::Arc<ItemReading>,
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
    pub said_finite: crate::citing::finite::SaidFinite,
    /// The number system each set letter of numbers holds, D of `D ⊆ ℝ` or
    /// c of `{1, …, i} ∖ c` (`citing::number_sets::set_letter_systems`):
    /// what a backend whose sets are typed gives the letter.
    pub set_systems: IndexMap<String, crate::rules::System>,
    /// The number system each letter in scope at a step is introduced in,
    /// by the step's index (`library::introduced`): the narrower of two
    /// where a later line narrows it, q ∈ ℕ₀ of a q let in ℤ. What the
    /// said-once walk reads letters by (`citing::reason`), so that a backend
    /// asking it of a term asks with the checker's letters.
    pub introduced: Vec<crate::citing::Introduced>,
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
    pub joined: IndexMap<usize, Vec<Vec<FirstAt>>>,
    /// What each `exhibit` step shows, by the line of its justification: for each
    /// sentence of its claim, the values of its "there is" and where each
    /// fact it says of them stands (`citations::exhibit_values`).
    pub exhibited: IndexMap<usize, Vec<Option<Exhibit>>>,
    /// How each obtain step's sentences after its memberships are the parts
    /// of the "there is" it obtains from, by the line of its justification
    /// (`citations::obtained_parts`).
    pub obtained_parts: IndexMap<usize, Vec<ObtainedPart>>,
    /// How each instantiation's instance reaches its claim, a step's, a
    /// calculation row's or a requires line's, by the line of its
    /// justification
    /// (`citations::instantiations`).
    pub instantiated: IndexMap<usize, Instantiated>,
    /// Where each `restate` step's claim, and each requires line reasoned
    /// from lines alone, stands in a line it names, a "for all" read at a
    /// block's letter among them, by the line of its justification
    /// (`citations::restatements`).
    pub restated: IndexMap<usize, FirstAt>,
    /// How each calculation link citing a define, and each step whose reason
    /// is defines, meets the defines written out: its equation's two sides
    /// once each define's name is its value, a "for all"'s at its body; None
    /// where they do not meet and arithmetic is left. By the link's or the
    /// step's line (`formulas::define_link_meetings`).
    pub define_links: IndexMap<usize, Option<crate::matching::Meeting>>,
    /// Of each step citing a define by cases whose value it claims in one
    /// case, how it reaches that case and meets it. By the step's line
    /// (`formulas::define_cases`).
    pub define_cases: IndexMap<usize, TakenCase>,
    /// Of each step citing a function a define lets on a domain, `H(x) for
    /// x ∈ A ∪ B`, or substituting the define's equation at an argument,
    /// what says the argument it applies the function at is in that domain.
    /// By the step's line (`citations::define_domains`).
    pub define_domains: IndexMap<usize, DomainSaid>,
    /// Where in the line each calculation link cites the link stands, by
    /// the link's line (`formulas::link_places`). A link read off a chain,
    /// a = c of a = b = c, is placed at the chain's sentence with the pair it
    /// reads as `written`.
    pub link_places: IndexMap<usize, FirstAt>,
    /// Which way each calculation link that cites a line faces what the line
    /// says, an equation of the line's turned round where the link writes
    /// its sides the other way (`citations::facing_of`), by the link's line
    /// (`formulas::link_places`); left out where the line says no equation
    /// or no side meets.
    pub link_facings: IndexMap<usize, Facing>,
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
    /// How each step that ends a block, a part of one or the proof meets
    /// what it owes, by the line of its justification: one meeting for each
    /// part of its "and" in order (`formulas::ended_meetings`).
    pub ends_met: IndexMap<usize, Vec<crate::matching::Meeting>>,
    /// Each term a step puts where a notation asks a number system, a of
    /// a ≡ b (mod n) in ℤ, with how the step shows it is in that system
    /// (`formulas::check_place_systems`), by the step's index: so that a
    /// backend proves the membership as the check found it.
    pub places_shown: Vec<Vec<PlaceShown>>,
    /// The letters the reason under a function's define that says a kind of
    /// number is read with, by the define's label: the step's below it, and
    /// the define's argument in the set it runs over, as the check reads
    /// the reason, a step said of every member (`check_kinds`).
    pub kind_letters: IndexMap<String, crate::citing::Introduced>,
    /// Each claim the `membership` method proves, by the line its reason
    /// is on, whose term is in its system beside an equation a line it
    /// names says (`ShownBy::Beside`): a^(p − 1) ∈ ℤ from a^(p − 1) =
    /// a^(p − 2)·a and a^(p − 2) ∈ ℤ. A backend proves it the same way.
    pub members_shown: IndexMap<usize, PlaceShown>,
    /// The parts of the terms a reason's claim and lines write that the
    /// lines it names put in a number system, each with how, by the line
    /// the reason is on: a step's, or a requires line's
    /// (`formulas::held_by_lines`). The said-once walk takes a term apart
    /// into its parts and reads each here, so that a backend names a part
    /// whole from the line the check found, m of m² from `m ∈ ℕ`, and from
    /// no line the reason does not name.
    pub held_by_lines: IndexMap<usize, Vec<HeldByLines>>,
    /// Each "for all" a line a step may cite says that the step reads at a
    /// block's letter, with that letter, by the step's index
    /// (`Known::letters_read_at`): 5.6's "for all a ∈ {2, …, p − 2}, f(a) ∈
    /// ℤ" says f(a) ∈ ℤ at the a of the block 5.7 stands in. A backend
    /// reads the line at the letter the check read it at.
    pub read_at: Vec<Vec<ReadAt>>,
    /// What the statement's hypotheses bound below, y − 3 ≥ 0 of `y ≥ 3`
    /// (`citing::bounds`), read with the letters the header lets.
    pub statement_bounds: crate::citing::bounds::SaidBounds,
    /// What the lines in scope at each step bound below, by the step's
    /// index, read with the step's letters (`checker::bounds`). A backend
    /// writes a square root or a real power of a base at least 0 as a real
    /// one, as Metamath proves `√x ∈ ℝ` from `0 ≤ x`.
    pub bounds: Vec<crate::citing::bounds::SaidBounds>,
    /// The sets the lines in scope at each step say are finite in words,
    /// `W is finite` or `B ⊆ A` of a finite A, as printed, each with why,
    /// by the step's index (`citing::finite::finite_sets_in_words`): a
    /// count of one is a natural number from there on, as of one
    /// `said_finite` holds.
    pub finite_at: Vec<crate::citing::finite::FiniteSets>,
    /// The number system each letter the page's lines put in sets of
    /// numbers is in, the widest of them, A of `let A be an element` and
    /// `A ∈ ℝ ∖ ℚ` (`citing::number_sets::element_systems`): what a backend
    /// whose letters are typed gives the letter.
    pub element_systems: IndexMap<String, crate::rules::System>,
    /// The function letters the page's lines give a type between sets of
    /// numbers, f of `f : D → ℝ`, with the systems of the domain and the
    /// codomain (`citing::number_sets::function_systems`).
    pub function_systems: IndexMap<String, crate::citing::number_sets::Between>,
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
    pub system: crate::rules::System,
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

/// A term a step puts where a notation asks a number system, and how the
/// step shows it is in that system.
#[derive(Clone, Debug)]
pub struct PlaceShown {
    pub term: Node,
    pub system: crate::rules::System,
    pub by: ShownBy,
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
    /// For an obtain, the sentence of the group that says the "there is",
    /// by its place among the group's sentences (`Taken::obtained`).
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
    /// Where the facts the citation's readings are taken from stand
    /// (`Taken::firsts`), found as a hypothesis the citation needs is
    /// (`supplied`): the cited line, or the sentence of it, a definition is
    /// unfolded from; else a requires line, or the `let` line that says a
    /// membership once. A fact nothing supplies has none.
    pub firsts: Vec<SuppliedBy>,
    /// What supplies each hypothesis of the group the citation takes, in
    /// the group's order: the fact the search took for it (`supplier`),
    /// and where that fact stands.
    pub supplied: Vec<Supplied>,
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
    /// elements dropped among it, x − 0 read as x; None where the two were
    /// not met as wholes.
    pub meetings: Vec<Option<crate::matching::Meeting>>,
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

/// One part of what a definition's right side asks, at a citation's values
/// (`Cited::unfolded`).
#[derive(Clone, Debug)]
pub enum Unfolded {
    /// A fact, and what supplies it.
    Fact { fact: Node, by: SuppliedBy },
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
    pub meeting: crate::matching::Meeting,
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
    pub meeting: crate::matching::Meeting,
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
    pub implied: Option<crate::citing::Implication>,
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
    pub meeting: crate::matching::Meeting,
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
        implied: crate::citing::Implication,
        written: Node,
    },
    /// One of the step's own requires lines above the one the fact is
    /// for, by its place among them, counted from 0, or what it implies.
    Requires {
        line: usize,
        implied: Option<crate::citing::Implication>,
    },
    /// What the member a claim said of every member is read at implies,
    /// `i ≥ 1` of `i ∈ ℕ`: the rule, and the fact as the page writes it.
    Member {
        implied: crate::citing::Implication,
        written: Node,
    },
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
    pub meeting: crate::matching::Meeting,
    /// Each value the step puts in a domain, in the order the line binds
    /// their letters, with where its membership of the domain stands
    /// (`citations::value_guards`).
    pub guards: Vec<Guard>,
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
    pub put: crate::matching::SubstitutionPlaces,
    /// How what the putting makes meets the claim (`Known::alike_how`): as
    /// written; with identity elements the putting makes and the claim
    /// leaves out, `1·x` written `x`; or turned round, `b ≡ c` of the claim
    /// `c ≡ b`, or a listed set's members in another order.
    pub meeting: crate::matching::Meeting,
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
    pub letter: crate::formula::symbol::Symbol,
    /// The number system the item takes it in, by its own hypothesis
    /// `x ∈ S`; None where it asks it in none.
    pub item_system: Option<crate::rules::System>,
    /// The narrowest number system the page says its value is in once;
    /// None for a value in none, a set or a function.
    pub value_system: Option<crate::rules::System>,
    /// For a letter that stands for a set, the number system its value is
    /// as a set, ℕ of `X := ℕ`; None for any other value.
    pub value_set: Option<crate::rules::System>,
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

/// What supplies one hypothesis of a cited item (`Cited::supplied`).
#[derive(Clone, Debug)]
pub struct Supplied {
    /// The hypothesis as the item's group asks it, in the item's letters.
    pub want: Node,
    pub by: SuppliedBy,
    /// Where the item writes the hypothesis, by which a backend that
    /// states the item finds it among its own; None for a fact that is no
    /// item's hypothesis, a value's domain or an exhibit's.
    pub at: Option<crate::citing::HypothesisAt>,
    /// How the fact the line writes met the hypothesis at the citation's
    /// values (`Known::alike_how`), as `Cited::meetings` records it for a
    /// conclusion: a listed set's members in another order, the identity
    /// elements dropped, the two sides turned. None where no line writes
    /// it.
    pub meeting: Option<crate::matching::Meeting>,
    /// Where the line says a "for all" over a set the hypothesis asks of a
    /// set inside it (`SYNTAX.md`; `citing::supply::narrowed`): "for all k ∈
    /// ℕ" for "for all k ∈ {1, …, n}". None where the two are over one set.
    pub narrowed: Option<Narrowed>,
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
        implied: Option<crate::citing::Implication>,
    },
    /// A `let` line in scope the step does not name: a membership said once
    /// where the letter is let, or what that membership implies.
    SaidOnce(FirstAt),
    /// No line: a membership the page says once of a term no `let` line
    /// writes, `k + 1 ∈ ℕ₀` of a k in ℕ₀, for the reason the said-once walk
    /// gives.
    Walked(crate::citing::SaidOnceFact),
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
    Identity(crate::matching::Meeting),
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

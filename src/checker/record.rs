//! What the checker decides about a theorem, once, for itself and for the
//! build: the block each step stands in and which part of it, each block's
//! steps and its last, the place each define is written in, the sort of
//! each name, the functions typed at each step, and the problems it finds.
//!
//! The build is handed this rather than working it out again as it walks
//! the proof, so the two cannot read one proof two ways.

use indexmap::IndexMap;

use crate::citing::Concluded;
use crate::corpus::{Step, StepNo, Theorem};
use crate::formula::{Node, Sorts};
use crate::outcome::Problem;

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
}

impl Block {
    /// The block's last step of its own: the last child, never a step of a
    /// block inside it.
    pub fn last(&self) -> Option<usize> {
        self.children.last().copied()
    }
}

/// A theorem as the checker reads it.
#[derive(Clone, Debug, Default)]
pub struct CheckedTheorem {
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
    /// Each step's citation of an item, by the step's index; None for a step
    /// that cites none, or whose citation no group of the item reads, which
    /// the checker reports.
    pub cited: Vec<Option<Cited>>,
    /// Each requires line's citation of an item, by the line it is on, read
    /// as the step the line would be (`requires_as_step`).
    pub cited_requires: IndexMap<usize, Cited>,
    /// The relation each line a `transitivity` step cites gives its chain,
    /// in the order cited, by the line the step is on: the line's own, or
    /// of a line saying several, the one that meets the chain.
    pub links: IndexMap<usize, Vec<Node>>,
}

/// A step's citation of an item as the checker reads it (`citing::taken`,
/// or `citing::obtained` for an obtain): the group of the item's
/// conclusions it takes, and what each of the item's letters stands for.
#[derive(Clone, Debug)]
pub struct Cited {
    /// The item, by its full name.
    pub item: String,
    pub group: usize,
    pub binding: IndexMap<String, Node>,
    /// The sentences of the item's conclusions the claim takes, and which
    /// way each is read, each sentence by its place among them all, counted
    /// across the groups in order: the place of the lemma that proves it in
    /// the item's target, which names one lemma to a sentence
    /// (`targets::clauses`). None for an obtain, which takes its group's
    /// "there is" whole.
    pub concluded: Vec<Concluded>,
    /// Where the facts the citation's readings are taken from stand
    /// (`Taken::firsts`): the cited line, or the sentence of it, a
    /// definition is unfolded from. A fact no line the citation names says,
    /// a membership said once among them, has none.
    pub firsts: Vec<FirstAt>,
    /// What the citation's own pairs make the item's letters, `n := b`, as
    /// the checker reads them (`Parts::seed`): what an obtain unfolds a
    /// definition at, where it claims no conclusion of the item.
    pub written: IndexMap<String, Node>,
}

/// A line a citation names that states a fact its reading is taken from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FirstAt {
    /// The line, by the reference that names it.
    pub line: String,
    /// The sentence of the line that states the fact, or a part of which
    /// does, counted from 0; None where the fact is the line's sentences
    /// together.
    pub sentence: Option<usize>,
    /// Where the fact is one part of the sentence's conjunction, which part,
    /// counted from 0 left to right with every conjunction taken apart
    /// (`citing::conjuncts`).
    pub part: Option<usize>,
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
                if step.number.len() > owner.len()
                    && step.number.prefix(owner.len()) == *owner
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
    /// step (`requires_as_step`) stands where its step does.
    pub fn index_of(thm: &Theorem, step: &Step) -> Option<usize> {
        thm.steps
            .iter()
            .position(|s| s.line == step.line)
            .or_else(|| {
                thm.steps
                    .iter()
                    .position(|s| s.requires.iter().any(|r| r.line == step.line))
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

    /// The step numbered `number` written nearest above `step`.
    pub fn written(thm: &Theorem, number: &StepNo, step: &Step) -> Option<usize> {
        thm.steps
            .iter()
            .rposition(|s| &s.number == number && s.line < step.line)
    }
}

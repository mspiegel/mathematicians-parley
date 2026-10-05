//! What each item asks a citation to supply, read once into patterns.

use std::cell::RefCell;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use crate::corpus::{Intro, Record, RecordKind, Theorem};
use crate::formula::{parse_here, Node, Sorts};
use crate::matching::{expand, Context};
use crate::regex;
use crate::sorts::{
    element_re, file_definitions, function_being_re, function_on_re, function_re,
    group_re, let_formula, part_re, polynomial_re, sentences, set_or_point_re, unlabel,
    Env,
};

/// One `then` group of an item.
pub struct Group {
    /// What it asks for, each fact with the text it was read from.
    pub wants: Vec<(String, Node)>,
    /// The sentences it concludes.
    pub gives: Vec<Node>,
}

/// A theorem this corpus proves, as a citation of it reads it: the theorem,
/// and the sort of each name its statement settles.
#[derive(Clone, Copy)]
pub struct Proved<'a> {
    pub thm: &'a Theorem,
    pub sorts: &'a Sorts,
}

/// What each item asks a citation to supply.
///
/// Only the hypotheses that are facts. `let X be a set`, `let P be a point`
/// and a function type declare a variable and are filled by the
/// instantiation, which is what Metamath calls a floating hypothesis; a
/// membership and an `assume` are essential and a step citing the item has
/// to supply them.
///
/// A record with two `then` groups states each conclusion under the
/// hypotheses written above it, so the groups are kept apart and a citation
/// satisfies any one of them. Items are asked for by their full name.
pub struct Library<'a> {
    pub env: Env<'a>,
    records: &'a [Record],
    /// The sort of each name an item record's statement uses, by the
    /// record's place in `records`.
    record_sorts: IndexMap<usize, Sorts>,
    items: IndexMap<String, usize>,
    proved: IndexMap<String, Proved<'a>>,
    cache: RefCell<IndexMap<String, Option<Rc<Vec<Group>>>>>,
    /// Which notations are an existential, a membership, a conjunction, a
    /// biconditional and an implication, taken from what they target in the
    /// kernel rather than named here.
    pub exists: IndexSet<String>,
    pub members: IndexSet<String>,
    pub conj: IndexSet<String>,
    pub bicond: IndexSet<String>,
    pub implies: IndexSet<String>,
    pub ctx: Context,
}

regex!(FIRST_WORD, r"^[a-z0-9-]+");

impl<'a> Library<'a> {
    /// `record_sorts` holds every item record's sorts, and `proved` gives
    /// the theorems a citation may name besides the records, each by its
    /// full name.
    pub fn new(
        records: &'a [Record],
        record_sorts: IndexMap<usize, Sorts>,
        proved: IndexMap<String, Proved<'a>>,
        env: Env<'a>,
    ) -> Library<'a> {
        let mut items = IndexMap::new();
        for (i, r) in records.iter().enumerate() {
            if r.kind.is_item() {
                items.insert(r.qualified(), i);
            }
        }
        let mut lib = Library {
            env,
            records,
            record_sorts,
            items,
            proved,
            cache: RefCell::new(IndexMap::new()),
            exists: IndexSet::new(),
            members: IndexSet::new(),
            conj: IndexSet::new(),
            bicond: IndexSet::new(),
            implies: IndexSet::new(),
            ctx: Context::new(&env.g.notations, records),
        };
        // A metamath field may say more after the target, as "wrex, and wrex
        // under wn" does, so the target is its first word.
        for r in records {
            if r.kind != RecordKind::Notation {
                continue;
            }
            let Some(first) = FIRST_WORD.find(str::trim(r.field_or_empty("metamath")))
            else {
                continue;
            };
            let set = match first.as_str() {
                "wrex" => &mut lib.exists,
                "wcel" => &mut lib.members,
                "wa" => &mut lib.conj,
                "wb" => &mut lib.bicond,
                "wi" => &mut lib.implies,
                _ => continue,
            };
            set.insert(r.name.clone());
        }
        lib
    }

    /// The item of that full name, a record or a theorem this corpus proves.
    pub fn item(&self, name: &str) -> Option<crate::corpus::Item<'a>> {
        if let Some(&i) = self.items.get(name) {
            return Some(crate::corpus::Item::Record(&self.records[i]));
        }
        self.proved
            .get(name)
            .map(|k| crate::corpus::Item::Theorem(k.thm))
    }

    /// The groups of the item of that full name, or None where no item has
    /// it.
    pub fn groups(&self, name: &str) -> Option<Rc<Vec<Group>>> {
        if let Some(found) = self.cache.borrow().get(name) {
            return found.clone();
        }
        let found = self.read(name).map(Rc::new);
        self.cache
            .borrow_mut()
            .insert(name.to_string(), found.clone());
        found
    }

    /// What the `let` lines of the item of that full name say its functions
    /// map between, `g : D → ℝ`, as trees in the item's own letters. The
    /// groups leave these out, since a function the theorem has asks
    /// nothing; one the citing proof defines is asked it in a requires line.
    pub fn function_types(&self, name: &str) -> Vec<Node> {
        // A theorem's hypothesis is written with its `let`, as a proof file
        // has it, and a record's without.
        let (said, sorts): (Vec<(Intro, String)>, &Sorts) =
            if let Some(k) = self.proved.get(name) {
                let said = k
                    .thm
                    .hypotheses
                    .iter()
                    .map(|h| (h.kind, unlabel(&h.text[h.kind.as_str().len()..])))
                    .collect();
                (said, k.sorts)
            } else if let Some(&i) = self.items.get(name) {
                let said = self.records[i]
                    .hypotheses
                    .iter()
                    .map(|h| (h.kind, unlabel(&h.text)))
                    .collect();
                (said, &self.record_sorts[&i])
            } else {
                return Vec::new();
            };
        let lines: Vec<String> = said
            .into_iter()
            .filter(|(kind, _)| *kind == Intro::Let)
            .map(|(_, text)| str::trim(&text).to_string())
            .filter(|text| {
                function_re().is_match(text) && !function_being_re().is_match(text)
            })
            .collect();
        self.trees(&lines, sorts)
    }

    /// One (hypotheses, conclusion sentences) pair per `then` group.
    fn read(&self, name: &str) -> Option<Vec<Group>> {
        if let Some(k) = self.proved.get(name) {
            let thm = k.thm;
            let lines: Vec<(Intro, String)> = thm
                .hypotheses
                .iter()
                .map(|h| {
                    let rest = &h.text[h.kind.as_str().len()..];
                    (h.kind, str::trim(&unlabel(rest)).to_string())
                })
                .collect();
            // A theorem's statement means what it meant in its own file: a
            // definition it names is written out there, so what cites it is
            // compared with the rule and never with a name of its own.
            let own = file_definitions(thm, self.env);
            let facts = self
                .facts(&lines, k.sorts)
                .into_iter()
                .map(|(text, tree)| (text, expand(&tree, &own)))
                .collect();
            let gives = self
                .trees(&sentences(&thm.conclusion), k.sorts)
                .iter()
                .map(|t| expand(t, &own))
                .collect();
            return Some(vec![Group {
                wants: facts,
                gives,
            }]);
        }
        let &i = self.items.get(name)?;
        let item = &self.records[i];
        let sorts = &self.record_sorts[&i];
        let mut out = Vec::new();
        for (text, at) in &item.conclusions {
            let lines: Vec<(Intro, String)> = item
                .hypotheses
                .iter()
                .filter(|h| h.line < *at)
                .map(|h| (h.kind, str::trim(&unlabel(&h.text)).to_string()))
                .collect();
            out.push(Group {
                wants: self.facts(&lines, sorts),
                gives: self.trees(&sentences(text), sorts),
            });
        }
        if out.is_empty() {
            out.push(Group {
                wants: Vec::new(),
                gives: Vec::new(),
            });
        }
        Some(out)
    }

    fn trees(&self, texts: &[String], sorts: &Sorts) -> Vec<Node> {
        texts
            .iter()
            .filter_map(|t| parse_here(t, self.env.g, sorts).ok())
            .collect()
    }

    fn facts(&self, lines: &[(Intro, String)], sorts: &Sorts) -> Vec<(String, Node)> {
        let mut out = Vec::new();
        for (kind, text) in lines {
            let mut text = text.clone();
            // A function's type is declared, and what `be` says of the
            // function is a fact like any other, asked for as `let y ∈ Y`
            // is: `let g : Y → X be one-to-one` asks that g be one-to-one.
            if *kind == Intro::Let
                && (function_being_re().is_match(&text)
                    || function_on_re().is_match(&text)
                    || polynomial_re().is_match(&text)
                    || part_re().is_match(&text))
            {
                text = let_formula(&text);
            } else if *kind == Intro::Let
                && (set_or_point_re().is_match(&text)
                    || function_re().is_match(&text)
                    || element_re().is_match(&text)
                    || group_re().is_match(&text))
            {
                continue;
            }
            if let Ok(tree) = parse_here(&text, self.env.g, sorts) {
                out.push((text, tree));
            }
        }
        out
    }
}

/// The facts, and each part of one that is a conjunction.
///
/// A line of two sentences supplies each, since a claim of several sentences
/// is their conjunction; a line saying `P and Q` is that same conjunction
/// written as one formula, and supplies each part the same way.
pub fn with_parts(facts: &[Node], library: &Library) -> Vec<Node> {
    let mut out: Vec<Node> = facts.to_vec();
    for fact in facts {
        for part in conjuncts(fact, library) {
            if out.iter().all(|x| part.shape() != x.shape()) {
                out.push(part);
            }
        }
    }
    out
}

/// A conjunction taken apart. A claim may take one part of what it gets,
/// and a fact may supply one part of what is asked, because a line is a
/// conjunction at kernel level either way and the projection lives in the
/// method's expansion.
pub fn conjuncts(node: &Node, library: &Library) -> Vec<Node> {
    if library.conj.contains(&node.notation) && node.children.len() == 2 {
        let mut out = conjuncts(&node.children[0], library);
        out.extend(conjuncts(&node.children[1], library));
        return out;
    }
    vec![node.clone()]
}

/// (what a step may claim, what a fact must state first), for one sentence
/// of an item's conclusion.
///
/// `SYNTAX.md` gives the moves: a sentence may be claimed as it stands;
/// where it is "A ↔ B" and a fact states A the step may claim B, and the
/// other way round; where it is "if A then B" and a fact states A the step
/// may claim B.
pub fn readings(node: &Node, library: &Library) -> Vec<(Node, Vec<Node>)> {
    let mut out = vec![(node.clone(), Vec::new())];
    if node.children.len() == 2 {
        let (left, right) = (&node.children[0], &node.children[1]);
        if library.bicond.contains(&node.notation) {
            out.push((right.clone(), vec![left.clone()]));
            out.push((left.clone(), vec![right.clone()]));
        } else if library.implies.contains(&node.notation) {
            out.push((right.clone(), vec![left.clone()]));
        }
    }
    out
}

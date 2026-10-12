//! What each item asks a citation to supply, read once into patterns.

use std::cell::RefCell;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use crate::corpus::{Intro, Record, RecordKind, Theorem};
use crate::formula::page::Written;
use crate::formula::{Node, Sorts};
use crate::matching::{expand, standard, Context};
use crate::regex;
use crate::sorts::introduction::{Form, Introduction};
use crate::sorts::{sorts_of_statement, statement_definitions, Env};

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
    /// biconditional, an implication and a negation, taken from what they
    /// target in the kernel rather than named here.
    pub exists: IndexSet<String>,
    pub members: IndexSet<String>,
    pub conj: IndexSet<String>,
    pub bicond: IndexSet<String>,
    pub implies: IndexSet<String>,
    pub negations: IndexSet<String>,
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
        let ctx = Context::new(&env.g.notations, records);
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
            negations: IndexSet::new(),
            ctx,
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
                "wn" => &mut lib.negations,
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

    /// The names a graph given in full in a `let` line of the theorem of
    /// that full name gives: the graph, its vertices and edges, and each
    /// vertex and edge it lists. They are no letters a citation chooses: the
    /// line lists those things, and a step citing the theorem means by each
    /// name what it means by it itself, as the elaborator reads it
    /// (`cite_corpus`). Left free, the listed names are matched every way
    /// the graph's symmetries allow, and Königsberg's seven bridges allow
    /// more than a search can try.
    pub fn listed_names(&self, name: &str) -> Vec<String> {
        let Some(k) = self.proved.get(name) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for h in k.thm.hypotheses.iter().filter(|h| h.kind == Intro::Let) {
            let introduced = Introduction::read(h.body(&k.thm.path));
            if let Form::GraphListed(line) = introduced.form {
                out.extend([
                    line.graph.clone(),
                    line.vertices.clone(),
                    line.edges.clone(),
                ]);
                if let Some(listing) = &line.listed {
                    out.extend(listing.vertices.iter().cloned());
                    out.extend(listing.edges.iter().cloned());
                }
            }
        }
        out
    }

    /// What the `let` lines of the item of that full name say its functions
    /// map between, `g : D → ℝ`, as trees in the item's own letters. The
    /// groups leave these out, since a function the theorem has asks
    /// nothing; one the citing proof defines is asked it in a requires line.
    pub fn function_types(&self, name: &str) -> Vec<Node> {
        // A theorem's hypothesis is written with its `let`, as a proof file
        // has it, and a record's without.
        let (said, sorts): (Vec<(Intro, Written)>, &Sorts) =
            if let Some(k) = self.proved.get(name) {
                let said = k
                    .thm
                    .hypotheses
                    .iter()
                    .map(|h| (h.kind, h.body(&k.thm.path)))
                    .collect();
                (said, k.sorts)
            } else if let Some(&i) = self.items.get(name) {
                let record = &self.records[i];
                let said = record
                    .hypotheses
                    .iter()
                    .map(|h| (h.kind, h.body(&record.path)))
                    .collect();
                (said, &self.record_sorts[&i])
            } else {
                return Vec::new();
            };
        let lines: Vec<Written> = said
            .into_iter()
            .filter(|(kind, _)| *kind == Intro::Let)
            .map(|(_, body)| body)
            .filter(|body| {
                matches!(Introduction::read(body.clone()).form, Form::Function)
            })
            .collect();
        self.trees(&lines, sorts)
    }

    /// One (hypotheses, conclusion sentences) pair per `then` group.
    fn read(&self, name: &str) -> Option<Vec<Group>> {
        if let Some(k) = self.proved.get(name) {
            let thm = k.thm;
            let lines: Vec<(Intro, Written)> = thm
                .hypotheses
                .iter()
                .map(|h| (h.kind, h.body(&thm.path)))
                .collect();
            // A theorem's statement means what it meant in its own file: a
            // definition it names is written out there, so what cites it is
            // compared with the rule and never with a name of its own.
            let own = statement_definitions(
                thm,
                self.env,
                &sorts_of_statement(thm, self.env),
            );
            let facts = self
                .facts(&lines, k.sorts)
                .into_iter()
                .map(|(text, tree)| (text, expand(&tree, &own)))
                .collect();
            let conclusion =
                Written::new(&thm.conclusion, &thm.path, thm.conclusion_line);
            let gives = self
                .trees(&[conclusion], k.sorts)
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
            let lines: Vec<(Intro, Written)> = item
                .hypotheses
                .iter()
                .filter(|h| h.line < *at)
                .map(|h| (h.kind, h.body(&item.path)))
                .collect();
            out.push(Group {
                wants: self.facts(&lines, sorts),
                gives: self.trees(&[Written::new(text, &item.path, *at)], sorts),
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

    /// Each sentence of what is written, read, in the standard order a
    /// citation is compared in (`matching::standard`). A sentence that does
    /// not read is `check_statements`'s to report.
    fn trees(&self, written: &[Written], sorts: &Sorts) -> Vec<Node> {
        written
            .iter()
            .flat_map(Written::sentences)
            .filter_map(|s| s.read(self.env.g, sorts).ok())
            .map(|t| standard(&t, &self.ctx))
            .collect()
    }

    /// What each hypothesis asks of a citation, by the sentence that says
    /// it, read.
    fn facts(&self, lines: &[(Intro, Written)], sorts: &Sorts) -> Vec<(String, Node)> {
        let mut out = Vec::new();
        let mut keep =
            |text: String, tree: &Node| out.push((text, standard(tree, &self.ctx)));
        for (kind, body) in lines {
            if *kind != Intro::Let {
                for sentence in body.sentences() {
                    if let Ok(tree) = sentence.read(self.env.g, sorts) {
                        keep(sentence.text().to_string(), &tree);
                    }
                }
                continue;
            }
            let introduced = Introduction::read(body.clone());
            match &introduced.form {
                // A thing named of a sort, and a function's type, are
                // declared and asked for by nothing.
                Form::Set(_)
                | Form::Point(_)
                | Form::Function
                | Form::Element(_)
                | Form::Group { .. }
                | Form::Graph(_) => {}
                // What `be` says of a function is a fact like any other,
                // asked for as `let y ∈ Y` is: `let g : Y → X be one-to-one`
                // asks that g be one-to-one. A part, a function on a set, a
                // polynomial and a graph given in full say what they are the
                // same way; a graph's listed names are the citing proof's
                // (`listed_names`).
                Form::FunctionBeing { .. }
                | Form::FunctionOn { .. }
                | Form::Polynomial(_)
                | Form::GraphListed(_)
                | Form::Part { .. } => {
                    // A part that does not read is `check_statements`'s to
                    // report.
                    for tree in
                        introduced.asserted(self.env.g, sorts).unwrap_or_default()
                    {
                        keep(self.env.g.print(&tree), &tree);
                    }
                }
                _ => {
                    for sentence in body.sentences() {
                        if let Ok(tree) = sentence.read(self.env.g, sorts) {
                            keep(sentence.text().to_string(), &tree);
                        }
                    }
                }
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

/// The ways a pattern may be read: as written, and where it is an equation
/// or the denial of one, turned round, since its sides say the same either
/// way (`SYNTAX.md`). Which way a pattern is read is decided by what the
/// search matches after it as much as by what it is matched with, so the
/// search tries each, where a match of one tree commits to the first way
/// that fits.
pub fn either_way(node: &Node, library: &Library) -> Vec<Node> {
    let turn = |eq: &Node| -> Option<Node> {
        (library.ctx.equations.contains(&eq.notation) && eq.children.len() == 2).then(
            || {
                let sides = vec![eq.children[1].clone(), eq.children[0].clone()];
                Node::new(&eq.notation, eq.sort.clone(), sides, &eq.text)
            },
        )
    };
    let turned =
        if library.negations.contains(&node.notation) && node.children.len() == 1 {
            turn(&node.children[0]).map(|eq| {
                Node::new(&node.notation, node.sort.clone(), vec![eq], &node.text)
            })
        } else {
            turn(node)
        };
    match turned {
        Some(turned) if turned.shape() != node.shape() => vec![node.clone(), turned],
        _ => vec![node.clone()],
    }
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

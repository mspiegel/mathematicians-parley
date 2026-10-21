//! What each item asks a citation to supply, read once into patterns.

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::IndexMap;

use crate::corpus::{Intro, Record, RecordKind, Theorem};
use crate::formula::notation_id::NotationId;
use crate::formula::page::Written;
use crate::formula::Binds;
use crate::formula::{Node, Sorts};
use crate::matching::{expand, free_names, standard, Context, FxIndexMap, FxIndexSet};
use crate::methods::terms::Targets;
use crate::notations::{APPLICATION, APPLICATION_TO_TWO};
use crate::regex;
use crate::sorts::introduction::{Form, Introduction};
use crate::sorts::{sorts_of_statement, statement_definitions, Env};

use super::supply::names_of;
use crate::checker::record::ItemReading;

/// One `then` group of an item.
pub struct Group {
    /// What it asks for, each fact with the text it was read from.
    pub wants: Vec<(String, Node)>,
    /// The sentences it concludes.
    pub gives: Vec<Node>,
    /// The library's functions it applies, which are no letters of its: a
    /// citation of `lowest-terms-parts` cannot make denom stand for numer.
    pub functions: BTreeSet<String>,
    /// The identity each group the item lets names, which is no letter of
    /// its either: it is the identity of the citing proof's group, which
    /// the group's line names by the same word, as the elaborator reads it.
    /// A letter there, `x·y = e` would be met by any line, or by none, with
    /// e put for x·y.
    pub identities: BTreeSet<String>,
}

impl Group {
    /// The letters free in what the group asks for and concludes: the
    /// item's own, which a citation gives values for, and not those a
    /// binder in it holds.
    pub fn free_names(
        &self,
        binders: &FxIndexMap<NotationId, Binds>,
    ) -> BTreeSet<String> {
        self.wants
            .iter()
            .map(|(_, t)| t)
            .chain(&self.gives)
            .flat_map(|t| free_names(t, binders))
            .collect()
    }

    /// The group with each letter a binder in it holds, where the letter is
    /// free elsewhere in the group, spelt apart (`matching::bound_apart`):
    /// the item's free n and the n of its own "for all n ∈ ℕ, f(n) > 0" are
    /// two letters, and a citation puts its value for the free one only.
    fn bound_apart(self, binders: &FxIndexMap<NotationId, Binds>) -> Group {
        let free = self.free_names(binders);
        let used: BTreeSet<String> = self
            .wants
            .iter()
            .map(|(_, t)| t)
            .chain(&self.gives)
            .flat_map(|t| t.names())
            .collect();
        let apart = |t: &Node| crate::matching::bound_apart(t, &free, &used, binders);
        let wants = self
            .wants
            .iter()
            .map(|(s, t)| (s.clone(), apart(t)))
            .collect();
        let gives = self.gives.iter().map(apart).collect();
        Group {
            wants,
            gives,
            ..self
        }
    }

    /// The item's letters among the names in `trees`: each but the
    /// library's functions it applies and its groups' identities.
    pub fn letters(&self, trees: &[Node]) -> BTreeSet<String> {
        let mut out = names_of(trees);
        out.retain(|n| !self.functions.contains(n) && !self.identities.contains(n));
        out
    }
}

/// The identities the group lines among `lines` name.
fn group_identities(lines: &[(Intro, Written)]) -> BTreeSet<String> {
    lines
        .iter()
        .filter(|(kind, _)| *kind == Intro::Let)
        .filter_map(|(_, body)| match Introduction::read(body.clone()).form {
            Form::Group { identity, .. } => Some(identity),
            _ => None,
        })
        .collect()
}

/// The library's functions the trees apply: a name applied, `denom(x)`,
/// that the library defines and the item has in scope, and that no `let`
/// line of the item introduces as its own.
fn applied_functions<'t>(
    trees: impl IntoIterator<Item = &'t Node>,
    lines: &[(Intro, Written)],
    sorts: &Sorts,
    env: Env,
) -> BTreeSet<String> {
    let own: BTreeSet<String> = lines
        .iter()
        .filter(|(kind, _)| *kind == Intro::Let)
        .filter_map(|(_, body)| {
            Introduction::read(body.clone()).name().map(str::to_string)
        })
        .collect();
    let mut out = BTreeSet::new();
    for tree in trees {
        for node in tree.walk() {
            let (APPLICATION | APPLICATION_TO_TWO, Some(head)) =
                (node.notation(), node.children.first())
            else {
                continue;
            };
            if head.is_name()
                && env.g.functions.contains_key(head.text.as_str())
                && sorts.imported.contains(head.text.as_str())
                && !own.contains(head.text.as_str())
            {
                out.insert(head.text.to_string());
            }
        }
    }
    out
}

/// A theorem this corpus proves, as a citation of it reads it: the theorem,
/// and the sort of each name its statement settles. The checker lends the
/// sorts it read the whole theorem with; the build reads them off the
/// statement, which is all a citation reads, and owns them.
#[derive(Clone)]
pub struct Proved<'a> {
    pub thm: &'a Theorem,
    pub sorts: std::borrow::Cow<'a, Sorts>,
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
    record_sorts: Cow<'a, IndexMap<usize, Sorts>>,
    items: IndexMap<String, usize>,
    proved: IndexMap<String, Proved<'a>>,
    cache: RefCell<IndexMap<String, Option<Rc<Vec<Group>>>>>,
    /// Which notations are an existential, a universal, a membership, a
    /// conjunction, a biconditional, an implication and a negation, taken
    /// from what they target in the kernel rather than named here.
    pub exists: FxIndexSet<NotationId>,
    pub every: FxIndexSet<NotationId>,
    pub members: FxIndexSet<NotationId>,
    pub conj: FxIndexSet<NotationId>,
    pub bicond: FxIndexSet<NotationId>,
    pub implies: FxIndexSet<NotationId>,
    pub negations: FxIndexSet<NotationId>,
    pub ctx: Context,
    /// The notations' and library functions' targets, which the deciders
    /// read a term by (`methods::terms`).
    pub targets: Targets,
}

regex!(FIRST_WORD, r"^[a-z0-9-]+");

impl<'a> Library<'a> {
    /// `record_sorts` holds every item record's sorts, and `proved` gives
    /// the theorems a citation may name besides the records, each by its
    /// full name.
    pub fn new(
        records: &'a [Record],
        record_sorts: Cow<'a, IndexMap<usize, Sorts>>,
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
        let targets = Targets::of(env.g, records);
        let mut lib = Library {
            env,
            records,
            record_sorts,
            items,
            proved,
            cache: RefCell::new(IndexMap::new()),
            exists: FxIndexSet::default(),
            every: FxIndexSet::default(),
            members: FxIndexSet::default(),
            conj: FxIndexSet::default(),
            bicond: FxIndexSet::default(),
            implies: FxIndexSet::default(),
            negations: FxIndexSet::default(),
            ctx,
            targets,
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
                "wral" => &mut lib.every,
                "wcel" => &mut lib.members,
                "wa" => &mut lib.conj,
                "wb" => &mut lib.bicond,
                "wi" => &mut lib.implies,
                "wn" => &mut lib.negations,
                _ => continue,
            };
            set.insert(NotationId::of(&r.name));
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

    /// The sorts the item of that full name is read with, a record's or a
    /// theorem's this corpus proves: what each of its letters is.
    pub fn item_sorts(&self, name: &str) -> Option<&Sorts> {
        match self.items.get(name) {
            Some(i) => self.record_sorts.get(i),
            None => self.proved_sorts(name),
        }
    }

    /// The sorts a theorem this corpus proves, of that full name, is read
    /// with (`Proved`).
    pub fn proved_sorts(&self, name: &str) -> Option<&Sorts> {
        self.proved.get(name).map(|k| k.sorts.as_ref())
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
                (said, &*k.sorts)
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

    /// Every sentence of every item a citation may name, read with the
    /// item's own sorts, by where it is written: each hypothesis, a `let`
    /// line part by part (`Introduction::parts`), each conclusion, and each
    /// formula a record's target fills its lemma's letters with. The build
    /// reads an item from here, never again (`ItemReading`).
    pub fn item_readings(&self) -> ItemReading {
        let mut out = ItemReading::default();
        for (i, r) in self.records.iter().enumerate() {
            let Some(sorts) = self.record_sorts.get(&i) else {
                continue;
            };
            let lines = r.hypotheses.iter().map(|h| (h.kind, h.body(&r.path)));
            let mut said: Vec<Written> = hypothesis_parts(lines);
            said.extend(r.stated());
            let (_, fills) = crate::targets::lemma(r);
            said.extend(fills.values().map(|f| Written::new(f, &r.path, r.line)));
            self.read_into(&mut out, &said, sorts);
        }
        for k in self.proved.values() {
            let thm = k.thm;
            let lines = thm.hypotheses.iter().map(|h| (h.kind, h.body(&thm.path)));
            let mut said: Vec<Written> = hypothesis_parts(lines);
            said.push(thm.stated());
            self.read_into(&mut out, &said, &k.sorts);
        }
        out
    }

    /// Each sentence of `said`, read with `sorts`, kept in `out`.
    fn read_into(&self, out: &mut ItemReading, said: &[Written], sorts: &Sorts) {
        for sentence in said.iter().flat_map(Written::sentences) {
            let read = sentence.read(self.env.g, sorts);
            out.keep(&sentence, read);
        }
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
            let facts: Vec<(String, Node)> = self
                .facts(&lines, &k.sorts)
                .into_iter()
                .map(|(text, tree)| (text, expand(&tree, &own)))
                .collect();
            let conclusion =
                Written::new(&thm.conclusion, &thm.path, thm.conclusion_line);
            let gives: Vec<Node> = self
                .trees(&[conclusion], &k.sorts)
                .iter()
                .map(|t| expand(t, &own))
                .collect();
            let functions = applied_functions(
                gives.iter().chain(facts.iter().map(|(_, t)| t)),
                &lines,
                &k.sorts,
                self.env,
            );
            let group = Group {
                wants: facts,
                gives,
                functions,
                identities: group_identities(&lines),
            };
            return Some(vec![group.bound_apart(&self.ctx.binders)]);
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
            let wants = self.facts(&lines, sorts);
            let gives = self.trees(&[Written::new(text, &item.path, *at)], sorts);
            let functions = applied_functions(
                gives.iter().chain(wants.iter().map(|(_, t)| t)),
                &lines,
                sorts,
                self.env,
            );
            let group = Group {
                wants,
                gives,
                functions,
                identities: group_identities(&lines),
            };
            out.push(group.bound_apart(&self.ctx.binders));
        }
        if out.is_empty() {
            out.push(Group {
                wants: Vec::new(),
                gives: Vec::new(),
                functions: BTreeSet::new(),
                identities: BTreeSet::new(),
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

/// The parts of hypothesis lines that are formula text: a `let` line's
/// parts (`Introduction::parts`), and an `assume` line whole.
fn hypothesis_parts(lines: impl Iterator<Item = (Intro, Written)>) -> Vec<Written> {
    let mut out = Vec::new();
    for (kind, body) in lines {
        match kind {
            Intro::Let => out.extend(Introduction::read(body).parts()),
            _ => out.push(body),
        }
    }
    out
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
            if out.iter().all(|x| !part.same_shape(x)) {
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
    if library.conj.contains(&node.notation()) && node.children.len() == 2 {
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
        (library.ctx.equations.contains(&eq.notation()) && eq.children.len() == 2).then(
            || {
                let sides = vec![eq.children[1].clone(), eq.children[0].clone()];
                eq.with_children(sides)
            },
        )
    };
    let turned =
        if library.negations.contains(&node.notation()) && node.children.len() == 1 {
            turn(&node.children[0]).map(|eq| node.with_children(vec![eq]))
        } else {
            turn(node)
        };
    match turned {
        Some(turned) if !turned.same_shape(node) => vec![node.clone(), turned],
        _ => vec![node.clone()],
    }
}

/// Which way a sentence of an item's conclusion is read (`readings`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Way {
    /// The sentence claimed as it stands.
    AsWritten,
    /// "A ↔ B" or "if A then B", with A stated first and B claimed.
    Forward,
    /// "A ↔ B", with B stated first and A claimed.
    Backward,
}

/// One reading of a sentence of an item's conclusion.
pub struct Reading {
    /// What a step may claim.
    pub claimed: Node,
    /// What a fact must state first.
    pub first: Vec<Node>,
    pub way: Way,
}

/// Each reading of one sentence of an item's conclusion.
///
/// `SYNTAX.md` gives the moves: a sentence may be claimed as it stands;
/// where it is "A ↔ B" and a fact states A the step may claim B, and the
/// other way round; where it is "if A then B" and a fact states A the step
/// may claim B.
pub fn readings(node: &Node, library: &Library) -> Vec<Reading> {
    let mut out = vec![Reading {
        claimed: node.clone(),
        first: Vec::new(),
        way: Way::AsWritten,
    }];
    if node.children.len() == 2 {
        let (left, right) = (&node.children[0], &node.children[1]);
        if library.bicond.contains(&node.notation())
            || library.implies.contains(&node.notation())
        {
            out.push(Reading {
                claimed: right.clone(),
                first: vec![left.clone()],
                way: Way::Forward,
            });
        }
        if library.bicond.contains(&node.notation()) {
            out.push(Reading {
                claimed: left.clone(),
                first: vec![right.clone()],
                way: Way::Backward,
            });
        }
    }
    out
}

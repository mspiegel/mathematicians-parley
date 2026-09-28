//! Reading: a line of the page, as kernel terms.
//!
//! This is the first of the elaborator's six parts (`ELABORATION.md`, "How
//! the elaborator is built"). Given a line of the page and the notation
//! records, it produces kernel terms, with each name the page uses standing
//! for a kernel variable.
//!
//! What a name stands for is `names`, which the scopes change as blocks open
//! and close; which kernel variable a binder or a fixed name takes is decided
//! here, once, and kept in `bound_as`.

use indexmap::IndexMap;

use super::state::Elaborator;
use crate::corpus::proof::visible;
use crate::corpus::{cited_name, resolve, DefineLine, Item, Recursion, ScopeId, Step};
use crate::formula::{fits, parse, Node, Sort};
use crate::matching::{substitute, Binding as NodeBinding, Defined, Definitions};
use crate::outcome::Checked;
use crate::regex;
use crate::rules::NUMERALS;
use crate::sorts::{
    definition_sorts, element_re, file_definitions, function_being_re, function_on_re,
    group_re, let_formula, not_in_re, part_re, sentences, sorts_of_record,
    sorts_of_statement, unlabel, Env,
};
use crate::t;
use crate::targets;
use crate::text::repr;

regex!(BE_A, r"\s+be\s+a\s+(set|point)\b");
regex!(SUBGROUP, r"^(\S+)\s+is\s+a\s+subgroup\s+of\s+(\S+)$");

/// The class variables a theorem's `let` lines are given, in order.
pub const CLASS_NAMES: [&str; 8] = ["cA", "cB", "cC", "cD", "cE", "cF", "cG", "cH"];

/// Whether a hypothesis says a group has a subgroup: `H is a subgroup of G`.
pub fn is_subgroup(text: &str) -> bool {
    SUBGROUP.is_match(text)
}

/// What a hypothesis line claims, with its introduction read as one.
///
/// `let A be a set` and `let P be a point` introduce a name and state what
/// the sort means, and the notation that states it is what the database
/// declares. `let a ∉ X` and `let x be an element` claim no sort on the
/// page, and the kernel still wants the thing to be a set, not a proper
/// class; that sethood is apparatus (`READERS.md`, hidden entirely), so it is
/// added here and never written.
pub fn hypothesis_body(kind: &str, text: &str) -> String {
    let body = text.strip_prefix(kind).unwrap_or(text);
    if kind == "let" {
        let said = str::trim(&unlabel(body)).to_string();
        if let Some(m) = element_re().captures(&said) {
            return format!("{} is a set", &m[1]);
        }
        if let Some(m) = not_in_re().captures(&said) {
            return format!("{} is a set and {said}", &m[1]);
        }
        // The line gives the function's type and says what it is, and both
        // hold: an image under f asks the type (`fex`), a one-to-one lemma
        // the property.
        if let Some(m) = function_being_re().captures(&said) {
            return format!("{} and {}", &m[1], let_formula(&said));
        }
        if part_re().is_match(&said) || function_on_re().is_match(&said) {
            return let_formula(&said);
        }
        return BE_A
            .replace_all(body, |m: &regex::Captures| format!(" is a {}", &m[1]))
            .into_owned();
    }
    body.to_string()
}

/// A term already in kernel form, standing in a tree.
pub fn literal(rpn: &str) -> Node {
    Node::literal(rpn)
}

/// The leftmost leaf of a tree: the name a `let` line introduces.
pub fn subject_of(node: &Node) -> Node {
    let mut node = node.clone();
    while !node.children.is_empty() {
        node = node.children[0].clone();
    }
    node
}

impl<'a> Elaborator<'a> {
    /// What a hypothesis line says, as `hypothesis_body` gives it, read where
    /// the elaborator has got to.
    ///
    /// `let x be an element` says x is a set because the kernel's element of
    /// a set is one, and that is apparatus the page never writes. A name the
    /// text uses as a number, a point or a group element is not something
    /// `_ is a set` takes, and the line then says nothing of it: `x = x`,
    /// which introduces x as a hypothesis line does and claims nothing.
    pub fn hypothesis_formula(&self, kind: &str, text: &str) -> String {
        let body = hypothesis_body(kind, text);
        if kind == "let" {
            let said = str::trim(&unlabel(text.strip_prefix(kind).unwrap_or(text)))
                .to_string();
            if let Some(m) = element_re().captures(&said) {
                let name = &m[1];
                if self.sorts_now.get(name).is_some_and(|s| !fits("set", s)) {
                    return format!("{name} = {name}");
                }
            }
        }
        body
    }

    pub fn env(&self) -> Env<'a> {
        Env {
            g: self.g,
            scopes: self.scopes,
        }
    }

    /// Run `f` with what each name stands for given back afterwards.
    ///
    /// Reading a binder's body, a definition's right side, or an item cited
    /// at its instantiation binds names for as long as that reading lasts,
    /// and the proof's own meaning of each word comes back when it ends.
    pub fn names_kept<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let saved = self.names.clone();
        let out = f(self);
        self.names = saved;
        out
    }

    /// `names_kept`, giving back what each name was let into as well.
    pub fn names_and_sets_kept<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let saved = self.names.clone();
        let kept = self.sets.clone();
        let out = f(self);
        self.names = saved;
        self.sets = kept;
        out
    }

    /// Run `f` with the sorts an item's own lines state, and a theorem of the
    /// corpus read in its own file's definitions, written out.
    ///
    /// A name is what says which of two notations sharing a pattern is meant,
    /// and `|_|` is cardinality or absolute value according to what stands
    /// inside it. An item's hypotheses are written in its own names.
    pub fn in_its_names<T>(
        &mut self,
        item: Item<'a>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let kept = self.sorts_now.clone();
        let kept_written = self.from_outside.clone();
        let (written, own) = match item {
            Item::Theorem(t) => (
                file_definitions(t, self.env()),
                sorts_of_statement(t, self.env()),
            ),
            Item::Record(r) => (Definitions::new(), sorts_of_record(r, self.env())),
        };
        let mut sorts = kept.clone();
        for (k, v) in definition_sorts(&written) {
            sorts.insert(k, v);
        }
        for (k, v) in own {
            sorts.insert(k, v);
        }
        self.sorts_now = sorts;
        self.from_outside = written;
        let out = f(self);
        self.sorts_now = kept;
        self.from_outside = kept_written;
        out
    }

    /// One sentence of the readable layer, as a tree, read where the
    /// elaborator has got to: a formula that does not parse is a defect and
    /// wants somewhere to point.
    pub fn read(&self, text: &str) -> Checked<Node> {
        parse(
            str::trim(&unlabel(text)),
            self.g,
            &self.sorts_now,
            &self.thm.path,
            self.at,
        )
    }

    /// A tree as the kernel term it stands for.
    pub fn term(&mut self, node: &Node) -> Checked<String> {
        if let Some(rpn) = &node.literal {
            return Ok(rpn.to_string());
        }
        let applies_name = node.notation == "application"
            && node.children.len() == 2
            && node.children[0].is_name();
        // A step rule of a define by recursion speaks of the values at k,
        // which in set.mm are the parts of the state the step is applied to
        // (`recursion_terms`).
        if !self.recurring.is_empty() && applies_name {
            if let Some(part) = self.recurring.get(&node.children[0].text) {
                return Ok(part.clone());
            }
        }
        // A statement is read with the definitions from outside its theorem
        // written out, so what it says in set.mm never names them.
        if !self.from_outside.is_empty() && applies_name {
            if let Some(Defined::Rule(rule)) =
                self.from_outside.get(&node.children[0].text)
            {
                let mut put = NodeBinding::new();
                put.insert(rule.param.clone(), node.children[1].clone());
                let body = substitute(&rule.body, &put);
                return self.term(&body);
            }
        }
        if node.is_name() {
            if let Some(Defined::Term(t)) = self.from_outside.get(&node.text) {
                let t = t.clone();
                return self.term(&t);
            }
            return match self.names.get(&node.text) {
                Some(t) => Ok(t.clone()),
                // A name the proof never introduced, which is the text's to
                // fix wherever the reading of it came from.
                None => Err(self.defect(
                    self.at,
                    format!("no kernel name for {}", repr(&node.text)),
                )),
            };
        }
        if node.notation == "numeral" {
            // set.mm writes a numeral of several digits as decimals,
            // `; A B` with A the digits before the last: 10 is `; 1 0`.
            let digit = |c: char| -> &'static str {
                NUMERALS
                    .iter()
                    .find(|(d, _)| d.starts_with(c))
                    .map(|(_, l)| *l)
                    .unwrap_or("")
            };
            let mut chars = node.text.chars();
            let mut said = digit(chars.next().unwrap_or('0')).to_string();
            for c in chars {
                said = t!(said, digit(c), "cdc");
            }
            return Ok(said);
        }
        // A binder's first hole is the variable it introduces, which stands
        // for itself rather than for whatever a name is bound to.
        let bound = self
            .binders
            .get(&node.notation)
            .cloned()
            .unwrap_or_default();
        let holes = self.names_kept(|me| -> Checked<Vec<String>> {
            for &i in &bound {
                let said = node.children[i].text.clone();
                let var = me.binder_var(&said)?;
                me.names.insert(said, format!("{var} cv"));
            }
            let mut holes = Vec::new();
            for (i, c) in node.children.iter().enumerate() {
                holes.push(if bound.contains(&i) {
                    me.binder_var(&c.text)?
                } else {
                    me.term(c)?
                });
            }
            Ok(holes)
        })?;
        let pattern = self.pattern(node)?;
        Ok(targets::fill(&pattern, &holes))
    }

    /// The `target` entry of the pattern this node was built from.
    ///
    /// A notation with no target is a gap in `corpus/db/notation.records` and so a
    /// person's to fix, at the line that wrote the notation.
    pub fn pattern(&self, node: &Node) -> Checked<String> {
        let Some(entries) = self.terms.get(&node.notation) else {
            return Err(self.defect(
                self.at,
                format!("notation {} has no target field", repr(&node.notation)),
            ));
        };
        let order = self.literals.get(&node.notation);
        let at = order
            .and_then(|o| o.iter().position(|l| *l == node.text))
            .unwrap_or(0);
        let Some(found) = entries.get(at).cloned().flatten() else {
            return Err(self.defect(
                self.at,
                format!("notation {} builds no term here", repr(&node.notation)),
            ));
        };
        // A part of the group the theorem lets, which nothing on the page
        // names (`targets::contexts`).
        let mut found = found;
        let mut tokens: Vec<String> = Vec::new();
        for token in targets::contexts(&found) {
            if !tokens.iter().any(|t| t == token) {
                tokens.push(token.to_string());
            }
        }
        for token in tokens {
            let Some(stands) = self.names.get(&token) else {
                return Err(self.defect(
                    self.at,
                    format!(
                        "{} needs a group, and no `let` line gives one",
                        node.notation
                    ),
                ));
            };
            let alone = fancy_regex::Regex::new(&format!(
                r"(?<!\S){}(?!\S)",
                regex::escape(&token)
            ))
            .expect("a token as a pattern");
            found = alone
                .replace_all(&found, fancy_regex::NoExpand(stands))
                .into_owned();
        }
        Ok(found)
    }

    /// The item a citation in this theorem's file names: `def:x` or `thm:x`,
    /// spelt with its file's path, or bare for a theorem of this file.
    pub fn item_cited(&self, cited: &str) -> Item<'a> {
        let name = resolve(cited_name(cited), self.thm.module());
        *self
            .items
            .get(&name)
            .unwrap_or_else(|| panic!("no item {name}"))
    }

    /// The same equality with its sides the other way round.
    pub fn flip(node: &Node) -> Node {
        let mut kids = node.children.clone();
        kids.reverse();
        Node::new(&node.notation, node.sort.clone(), kids, &node.text)
    }

    /// A definition's right side, as nodes, with its names bound.
    ///
    /// Returns the unfolding lemma, the bound variable, the node the
    /// existential quantifies (facing the way the lemma writes it), the same
    /// as the text faces it, what it quantifies over, and the left side.
    pub fn definition(
        &mut self,
        name: &str,
        subject: &str,
        var: Option<String>,
    ) -> Checked<(String, String, Node, Node, String, String)> {
        let Item::Record(item) = self.item_cited(name) else {
            panic!("{name} is a definition of the database");
        };
        let (lemma, flipped) = targets::unfolding(item);
        let Some(lemma) = lemma else {
            return Err(self.defect(self.at, format!("{name} has no target field")));
        };
        let var = match var {
            Some(v) => v,
            None => {
                let bound = self
                    .sig(&lemma)
                    .bound()
                    .expect("a lemma that binds")
                    .to_string();
                self.float_of(&bound)
            }
        };
        let node = self.read(&item.conclusions[0].0)?;
        let (left, right) = (node.children[0].clone(), node.children[1].clone());
        self.names
            .insert(subject_of(&left).text.clone(), subject.to_string());
        self.names
            .insert(right.children[0].text.clone(), format!("{var} cv"));
        let body = right.children[2].clone();
        let faces = if flipped {
            Self::flip(&body)
        } else {
            body.clone()
        };
        let over = self.term(&right.children[1])?;
        let said = self.term(&left)?;
        Ok((lemma, var, faces, body, over, said))
    }

    /// What the step writes for the letter a definition is about, found by
    /// that letter's name among its `v := t` pairs (`SYNTAX.md`: a
    /// substitution names its variable). A step that gives the subject no
    /// value is refused: the pair is not optional.
    pub fn subject_given(
        &self,
        name: &str,
        pairs: &[(String, String)],
        line: usize,
    ) -> Checked<String> {
        let Item::Record(item) = self.item_cited(name) else {
            panic!("{name} is a definition of the database");
        };
        let left = self.read(&item.conclusions[0].0)?.children[0].clone();
        let letter = subject_of(&left).text.clone();
        let given: IndexMap<&str, &str> = pairs
            .iter()
            .map(|(a, b)| (a.as_str(), b.as_str()))
            .collect();
        match given.get(letter.as_str()) {
            Some(v) => Ok(v.to_string()),
            None => Err(self.defect(
                line,
                format!(
                    "{name} is about {letter}, and the step gives {letter} no value; write it, as {letter} := t"
                ),
            )),
        }
    }

    pub fn sentences(&self, text: &str) -> Vec<String> {
        sentences(&unlabel(text))
    }

    /// A claim of several sentences is their conjunction, in the order the
    /// text writes them: the kernel has one conclusion.
    pub fn claim_of(&mut self, text: &str) -> Checked<String> {
        let mut said = Vec::new();
        for s in self.sentences(text) {
            let node = self.read(&s)?;
            said.push(self.term(&node)?);
        }
        let mut whole = said[0].clone();
        for extra in &said[1..] {
            whole = t!(whole, extra, "wa");
        }
        Ok(whole)
    }

    /// Name every `let` variable, and read the hypotheses.
    ///
    /// A `let` introduces a name and says what it ranges over, and all three
    /// forms name the thing they introduce first, so all three are read the
    /// same way: name the leftmost leaf, then read the line as a claim about
    /// it.
    pub fn hypotheses(&mut self) -> Checked<Vec<Node>> {
        let mut nodes = Vec::new();
        let mut spare: Vec<&str> = CLASS_NAMES.to_vec();
        for h in &self.thm.hypotheses {
            let kind = h.kind.as_str();
            let rest =
                str::trim(&unlabel(h.text.strip_prefix(kind).unwrap_or(&h.text)))
                    .to_string();
            if kind == "let" {
                if let Some(group) = group_re().captures(&rest) {
                    let structure = spare.remove(0);
                    nodes.push(self.group(&group, structure));
                    continue;
                }
            }
            let node = self.read(&self.hypothesis_formula(kind, &h.text))?;
            // `assume H is a subgroup of G` introduces H as a `let` would.
            let subgroup = kind == "assume" && SUBGROUP.is_match(&rest);
            if kind == "let" || subgroup {
                let introduced = subject_of(&node);
                if !introduced.text.is_empty()
                    && !self.names.contains_key(&introduced.text)
                {
                    self.names
                        .insert(introduced.text.clone(), spare.remove(0).to_string());
                }
                if node.notation == "membership" {
                    let set = self.term(&node.children[1])?;
                    self.sets.insert(introduced.text.clone(), set);
                }
            }
            nodes.push(node);
        }
        Ok(nodes)
    }

    /// The hypothesis a group's `let` line states, with its names given.
    ///
    /// set.mm's group is a structure: a class W whose `Base` is the set,
    /// whose `+g` is the operation and whose `0g` is the identity, and the
    /// hypothesis is that W is a group. The page never writes W.
    fn group(&mut self, said: &regex::Captures, structure: &str) -> Node {
        let part = |label: &str| t!(structure, label, "cfv");
        self.names.insert(said["group"].to_string(), part("cbs"));
        self.names.insert(said["identity"].to_string(), part("c0g"));
        for (name, label) in [
            ("@op", "cplusg"),
            ("@inv", "cminusg"),
            ("@subgroups", "csubg"),
            ("@lsm", "clsm"),
        ] {
            self.names.insert(name.to_string(), part(label));
        }
        let mut claim = t!(structure, "cgrp", "wcel");
        if said.name("finite").is_some() {
            let base = self.names[&said["group"]].clone();
            claim = t!(claim, t!(base, "cfn", "wcel"), "wa");
        }
        literal(&claim)
    }

    /// (name, define, scope) for each definition the theorem sees from
    /// outside it: those its file writes above it and those it imports.
    pub fn visible_outside(&self) -> Vec<(String, DefineLine, ScopeId)> {
        visible(self.scopes, self.thm.scope, self.thm.line)
    }

    /// The label a definition from outside the theorem is held under: its own
    /// where its file is this theorem's, and the label on the import where it
    /// is imported, so a step cites it as the page does.
    pub fn outside_label(&self, name: &str, d: &DefineLine, src: ScopeId) -> String {
        if src == self.thm.scope {
            d.label.clone()
        } else {
            self.scopes[self.thm.scope]
                .import_label(name)
                .unwrap_or_else(|| panic!("no import writes {name}"))
                .to_string()
        }
    }

    /// A definition from outside the theorem, written out, as a term: its
    /// rule, or for a function the map from its domain to its rule.
    pub fn outside_term(&mut self, made: &Defined) -> Checked<String> {
        let rule = match made {
            Defined::Term(t) => {
                let said = self.term(t)?;
                return self.apart(&said);
            }
            Defined::Rule(rule) => rule.clone(),
        };
        let var = self.binder_var(&rule.param)?;
        let (body, over) = self.names_kept(|me| -> Checked<(String, String)> {
            me.names.insert(rule.param.clone(), format!("{var} cv"));
            let body = me.term(&rule.body)?;
            let domain = me.read(rule.domain.as_deref().unwrap_or(""))?;
            let over = me.term(&domain)?;
            Ok((body, over))
        })?;
        self.apart(&t!(var, over, body, "cmpt"))
    }

    /// Each name a define by recursion gives, as its set.mm term: the map
    /// from ℕ₀ sending k to that name's part of the recursion's value at k.
    /// Written once per define and kept, so the statement and the proof
    /// speak of one recursion.
    ///
    /// The n values are one state: the value itself for one sequence, a pair
    /// for two, and for more a pair whose second is the rest. The recursion
    /// is set.mm's `seq 0 ((E ∘ 1st), (ℕ₀ × {start}))`.
    pub fn recursion_terms(
        &mut self,
        label: &str,
        said: &Recursion,
    ) -> Checked<IndexMap<String, String>> {
        if let Some(maps) = self.recursion_maps.get(label) {
            return Ok(maps.clone());
        }
        let state = self.spare_var()?;
        let index = self.spare_var()?;
        let count = said.names.len();
        let parts = |of: String| -> Vec<String> {
            let mut out = Vec::new();
            let mut of = of;
            for _ in 1..count {
                out.push(t!(of, "c1st", "cfv"));
                of = t!(of, "c2nd", "cfv");
            }
            out.push(of);
            out
        };
        fn tuple_of(values: &[String]) -> String {
            if values.len() == 1 {
                return values[0].clone();
            }
            t!(values[0], tuple_of(&values[1..]), "cop")
        }
        let mut starts = Vec::new();
        for name in &said.names {
            let node = self.read(&said.start[name])?;
            starts.push(self.term(&node)?);
        }
        let kept = self.recurring.clone();
        let kept_sorts = self.sorts_now.clone();
        self.recurring = said
            .names
            .iter()
            .cloned()
            .zip(parts(format!("{state} cv")))
            .collect();
        self.sorts_now
            .insert(said.index.clone(), Sort::of("number"));
        let steps = (|| -> Checked<Vec<String>> {
            let mut steps = Vec::new();
            for name in &said.names {
                let node = self.read(&said.step[name])?;
                steps.push(self.term(&node)?);
            }
            Ok(steps)
        })();
        self.recurring = kept;
        self.sorts_now = kept_sorts;
        let steps = steps?;
        let start = tuple_of(&starts);
        let step = t!(state, "cvv", tuple_of(&steps), "cmpt");
        let recursion = t!(
            t!(step, "c1st", "ccom"),
            t!("cn0", t!(start, "csn"), "cxp"),
            "cc0",
            "cseq"
        );
        self.recursions
            .insert(recursion.clone(), (step, start, count));
        let at_k = t!(format!("{index} cv"), recursion, "cfv");
        let maps: IndexMap<String, String> = said
            .names
            .iter()
            .cloned()
            .zip(parts(at_k))
            .map(|(name, part)| (name, t!(index, "cn0", part, "cmpt")))
            .collect();
        self.recursion_maps.insert(label.to_string(), maps.clone());
        Ok(maps)
    }

    /// A term whose bound names are ones nothing else is using.
    ///
    /// A `define` names a thing by a body that binds a name of its own, and
    /// the proof may go on to fix a name spelt the same way. Only the names
    /// the body binds are moved: a name the proof already holds keeps its
    /// meaning.
    pub fn apart(&mut self, rpn: &str) -> Checked<String> {
        let whole = self.to_term(rpn);
        let mut binding = crate::elab::state::Binding::new();
        let holds = self.names_held();
        for said in whole.names().iter() {
            let Some(label) = self.b.flabel.get(said).cloned() else {
                continue;
            };
            if !holds.contains(&label) && self.is_setvar(&label) {
                let fresh = self.spare_var()?;
                binding.insert(said.to_string(), self.var_of(&fresh));
            }
        }
        Ok(self.rpn(&whole.substitute(&binding)))
    }

    /// Every sentence of a step's claim, as trees.
    pub fn said(&self, step: &Step) -> Checked<Vec<Node>> {
        self.sentences(&step.claim_text())
            .iter()
            .map(|s| self.read(s))
            .collect()
    }

    /// What an item claims, from wherever its statement lives.
    pub fn claimed_by(item: Item) -> String {
        match item {
            Item::Theorem(t) => t.conclusion.clone(),
            Item::Record(r) => r.conclusions[0].0.clone(),
        }
    }

    /// The setvar a binder's name stands for: the letter's own label where
    /// it names a setvar, and a spare otherwise — the same one every time,
    /// since the name is one name wherever the proof writes it.
    pub fn binder_var(&mut self, name: &str) -> Checked<String> {
        if let Some(v) = self.bound_as.get(name) {
            return Ok(v.clone());
        }
        let label = match self.b.flabel.get(name) {
            Some(l) if self.is_setvar(l) => l.clone(),
            _ => self.spare_var()?,
        };
        self.bound_as.insert(name.to_string(), label.clone());
        self.written_as.insert(label.clone(), name.to_string());
        Ok(label)
    }

    /// The variable a fixed name takes: its own letter where nothing else is
    /// holding it, because the claim the block states binds that letter and
    /// the two have to agree; a spare otherwise.
    pub fn fixed_var(&mut self, name: &str, scope: &str) -> Checked<String> {
        let mut held = self.names_held();
        for t in scope.split_whitespace() {
            if self
                .b
                .sigs
                .get(t)
                .is_some_and(|s| s.kind == crate::mm::Kind::Float)
            {
                held.insert(t.to_string());
            }
        }
        let own = self.b.flabel.get(name).cloned();
        let own = match own {
            Some(o)
                if self.is_setvar(&o)
                    && !held.contains(&o)
                    && !self.taken.contains(&o) =>
            {
                o
            }
            _ => self.spare_var()?,
        };
        self.bound_as.insert(name.to_string(), own.clone());
        self.written_as.insert(own.clone(), name.to_string());
        Ok(own)
    }

    /// A kernel variable no name in this proof is already standing for.
    ///
    /// Running out is raised, not declined: it is the tool at its limit, a
    /// proof introducing more names than the kernel has letters.
    pub fn spare_var(&mut self) -> Checked<String> {
        let mut held = self.names_held();
        held.extend(self.reserved.iter().cloned());
        held.extend(self.bound_as.values().cloned());
        while !self.spare.is_empty() && held.contains(&self.spare[0]) {
            self.spare.remove(0);
        }
        if self.spare.is_empty() {
            return Err(
                self.defect(self.at, "no variable left to introduce a name with")
            );
        }
        Ok(self.spare.remove(0))
    }

    /// The tree with its leaves turned into the terms they stand for, so a
    /// definition's body means what it meant before the names change back.
    /// A binder's own variable is left alone: it stands for itself.
    pub fn freeze(&mut self, node: &Node) -> Checked<Node> {
        if node.children.is_empty() {
            let said = self.term(node)?;
            return Ok(literal(&said));
        }
        let bound = self
            .binders
            .get(&node.notation)
            .cloned()
            .unwrap_or_default();
        self.names_kept(|me| -> Checked<Node> {
            for &i in &bound {
                let said = node.children[i].text.clone();
                let var = me.binder_var(&said)?;
                me.names.insert(said, format!("{var} cv"));
            }
            let mut kids = Vec::new();
            for (i, c) in node.children.iter().enumerate() {
                kids.push(if bound.contains(&i) {
                    c.clone()
                } else {
                    me.freeze(c)?
                });
            }
            Ok(Node::new(
                &node.notation,
                node.sort.clone(),
                kids,
                &node.text,
            ))
        })
    }

    /// The node with one name replaced, for reading off the instance.
    pub fn substituted(&mut self, node: &Node, old: &str, new: &str) -> Checked<Node> {
        if self.term(node)? == old {
            return Ok(literal(new));
        }
        if node.children.is_empty() {
            return Ok(node.clone());
        }
        let mut kids = Vec::new();
        for c in &node.children {
            kids.push(self.substituted(c, old, new)?);
        }
        Ok(Node::new(
            &node.notation,
            node.sort.clone(),
            kids,
            &node.text,
        ))
    }
}

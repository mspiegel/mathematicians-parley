//! What each theorem's lines give the checks that read them.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::IndexMap;

use super::structure::{labels_in_scope, Declared};
use crate::citing::{
    claimed_member, finished, introduction, said_once, taken, with_parts, Introduced,
    Library, Parts,
};
use crate::corpus::proof::{cited_item, visible};
use crate::corpus::{Intro, Kinded, Method, Step, StepNo, Theorem, Values};
use crate::formula::page::{conjoined, filled, Sentence, Written};
use crate::formula::{Node, Sorts};
use crate::matching::{alike, expand, standard, Binding, Context, Definitions};
use crate::outcome::Built;
use crate::sorts::introduction::Introduction;
use crate::sorts::{cited_defines, file_definitions, Env};

type PartsKey = (StepNo, String, String, Vec<String>, Vec<String>);

/// Every line a step's citation may name, by the reference that names it,
/// with what the line says.
pub type Statements = IndexMap<String, Stated>;

/// What a line a citation may name says: formula text, a step's claim or
/// an assumption; or a `let` line's introduction, which asserts what its
/// form does (`Introduction::asserted`).
#[derive(Clone)]
pub enum Stated {
    Written(Written),
    Introduced(Introduction),
    /// A naming `let` that says what kind of number its name is, `let m =
    /// gcd(s, w), a natural number`: the name, and the number system the
    /// kind's record names, which the line says the name is in.
    Kind {
        name: Written,
        set: Written,
    },
    /// An induction hypothesis: what its induction's claim, "for all k ∈ X,
    /// …", says at its letter.
    Hypothesis(Written),
}

impl Stated {
    /// The line's text as written, for a message.
    pub fn text(&self) -> &str {
        match self {
            Stated::Written(w) => w.text(),
            Stated::Introduced(i) => i.body.text(),
            Stated::Kind { name, .. } => name.text(),
            Stated::Hypothesis(claim) => claim.text(),
        }
    }
}

/// What a theorem's lines give every check of it, read once a run.
///
/// The sort of each name depends on the theorem alone, what each `define`
/// stands for on the lines a citation names, the lines a citation may name
/// on its step, and what a step's citation supplies on the step. Each is
/// read the first time a check asks and kept for the run; nothing that uses
/// them changes them.
///
/// What a step's citation supplies is kept by what it depends on — the
/// step, its claim and reason, the lines it names and its requires lines —
/// so that a step with a
/// line taken away, as `check_surplus` asks about, is read afresh.
pub struct Known<'a> {
    pub thm: &'a Theorem,
    pub env: Env<'a>,
    pub sorts: Sorts,
    /// What the notations are, read once for the corpus: which spelling of a
    /// relation is another turned around (`matching::standard`).
    ctx: &'a Context,
    /// What each definition from outside the theorem stands for, written
    /// out where a citation names it.
    outside: Definitions,
    /// The label a citation names each definition from outside the theorem
    /// by: its own where its file is this theorem's, and the label on its
    /// import otherwise.
    outside_labels: IndexMap<String, String>,
    /// The labels of the defines this theorem's file writes above it.
    file_labels: Vec<String>,
    cited: RefCell<IndexMap<Vec<String>, Rc<Definitions>>>,
    scopes: RefCell<IndexMap<(StepNo, usize), Rc<Statements>>>,
    parts: RefCell<IndexMap<PartsKey, Rc<Parts>>>,
}

impl<'a> Known<'a> {
    /// `sorts` is what the theorem's one reading settled (`check::run`).
    pub fn new(
        thm: &'a Theorem,
        env: Env<'a>,
        sorts: Sorts,
        ctx: &'a Context,
    ) -> Known<'a> {
        let mut outside_labels = IndexMap::new();
        let mut file_labels = Vec::new();
        for (name, d, src) in visible(env.scopes, thm.scope, thm.line) {
            let label = if src == thm.scope {
                file_labels.push(d.label.clone());
                Some(d.label)
            } else {
                env.scopes[thm.scope].import_label(&name).map(String::from)
            };
            if let Some(label) = label {
                outside_labels.insert(name, label);
            }
        }
        Known {
            thm,
            env,
            sorts,
            ctx,
            outside: file_definitions(thm, env),
            outside_labels,
            file_labels,
            cited: RefCell::new(IndexMap::new()),
            scopes: RefCell::new(IndexMap::new()),
            parts: RefCell::new(IndexMap::new()),
        }
    }

    /// A sentence as the checks of `step` compare it: parsed with its sorts,
    /// each defined name the step's citation lets it write out written out
    /// (`citing`); None where it does not read, which `check_formulas`
    /// reports.
    pub fn read(&self, step: &Step, sentence: &Sentence) -> Option<Node> {
        self.read_citing(sentence, &self.citing_step(step))
    }

    /// Each sentence of a written part as the checks of `step` compare it
    /// (`read`), in the order written; one that does not read is left out,
    /// as `check_formulas` reports it.
    pub fn said(&self, step: &Step, written: &Written) -> Vec<Node> {
        written
            .sentences()
            .iter()
            .filter_map(|s| self.read(step, s))
            .collect()
    }

    /// A written part as one formula, as the checks of `step` compare it:
    /// its sentence, or the conjunction of its sentences, as a claim of
    /// several is one claim (`SYNTAX.md`); None where a sentence does not
    /// read, which `check_formulas` reports.
    pub fn whole(&self, step: &Step, written: &Written) -> Option<Node> {
        let sentences = written.sentences();
        let said: Vec<Node> = sentences
            .iter()
            .filter_map(|s| self.read(step, s))
            .collect();
        if said.len() != sentences.len() {
            return None;
        }
        conjoined(self.env.g, said)
    }

    /// A written part as one formula with its defined names kept (`whole`,
    /// `read_as_written`).
    pub fn whole_as_written(&self, written: &Written) -> Option<Node> {
        let read: Option<Vec<Node>> = written
            .sentences()
            .iter()
            .map(|s| self.read_as_written(s))
            .collect();
        conjoined(self.env.g, read?)
    }

    /// Each thing a line says, read: a sentence of what is written, or a
    /// formula its introduction asserts; with defined names kept, or with
    /// what `defined` writes out and in the standard order (`read_citing`).
    /// One that does not read is None, which `check_formulas` reports of a
    /// sentence and the elaborator of an introduction.
    pub fn said_parts(
        &self,
        stated: &Stated,
        defined: Option<&Definitions>,
    ) -> Vec<Option<Node>> {
        let cited = |n: Node| match defined {
            Some(d) => standard(&expand(&n, d), self.ctx),
            None => n,
        };
        match stated {
            Stated::Written(w) => w
                .sentences()
                .iter()
                .map(|s| self.read_as_written(s).map(cited))
                .collect(),
            Stated::Introduced(i) => match i.asserted(self.env.g, &self.sorts) {
                Ok(said) => said.into_iter().map(|n| Some(cited(n))).collect(),
                Err(_) => vec![None],
            },
            Stated::Kind { name, set } => {
                let read = |w: &Written| self.read_as_written(&w.sentence().ok()?);
                let member = match (read(name), read(set)) {
                    (Some(x), Some(s)) => {
                        let fills = [("x", &x), ("S", &s)];
                        filled("x ∈ S", self.env.g, &self.sorts, &fills).ok()
                    }
                    _ => None,
                };
                vec![member.map(cited)]
            }
            Stated::Hypothesis(claim) => {
                let statement = claim
                    .sentence()
                    .ok()
                    .and_then(|s| self.read_as_written(&s))
                    .and_then(|c| match (c.notation.as_str(), c.children.as_slice()) {
                        ("for-all", [_, _, body]) => Some(body.clone()),
                        _ => None,
                    });
                vec![statement.map(cited)]
            }
        }
    }

    /// What a line says, each thing read as the checks of `step` compare it
    /// (`read`); one that does not read is left out.
    pub fn stated_at(&self, step: &Step, stated: &Stated) -> Vec<Node> {
        let defined = self.citing_step(step);
        self.said_parts(stated, Some(&defined))
            .into_iter()
            .flatten()
            .collect()
    }

    /// The letters a formula binds for itself: each a binder holds, by what
    /// the grammar declares it holds (`for all c ∈ ℕ`, `{c ∈ A : …}`,
    /// `Σ(c = 1 to n)`).
    pub fn bound(&self, node: &Node) -> BTreeSet<String> {
        let binders = self.env.g.binders();
        let mut out = BTreeSet::new();
        for n in node.walk() {
            let Some(binds) = binders.get(&n.notation) else {
                continue;
            };
            for &at in &binds.held {
                if let Some(letter) = n.children.get(at).filter(|l| l.is_name()) {
                    out.insert(letter.text.clone());
                }
            }
        }
        out
    }

    /// A tree read as written, as the checks compare it once `defined` is
    /// written out (`read_citing`).
    pub fn as_cited(&self, node: &Node, defined: &Definitions) -> Node {
        standard(&expand(node, defined), self.ctx)
    }

    /// What a line says as one formula with its defined names kept: what it
    /// says, or the conjunction of the several things; None where a part
    /// does not read.
    pub fn stated_as_written(&self, stated: &Stated) -> Option<Node> {
        let read: Option<Vec<Node>> =
            self.said_parts(stated, None).into_iter().collect();
        conjoined(self.env.g, read?)
    }

    /// The sentence read with its defined names kept, as a message prints
    /// it; None where it does not read, which `check_formulas` reports.
    pub fn read_as_written(&self, sentence: &Sentence) -> Option<Node> {
        sentence.read(self.env.g, &self.sorts).ok()
    }

    /// Whether two readings are one formula: alike but for the letters they
    /// bind, the way round an equation is written (`matching::alike`), and
    /// the spelling of an order, `x > 0` for `0 < x` (`matching::standard`).
    /// The order of anything else, the two sides of an "or" among them, is
    /// kept: a disjunction has one pattern, and nothing turns it.
    pub fn alike(&self, a: &Node, b: &Node) -> bool {
        let none = IndexMap::new();
        alike(
            &standard(a, self.ctx),
            &standard(b, self.ctx),
            self.ctx,
            &none,
            &none,
        )
    }

    /// What a defined name stands for in a citation naming `refs`: each
    /// define the citation names, the theorem's own or one from outside it,
    /// which is named by its label in this file or the label its import
    /// gives. A defined name and the term it names are one formula in a step
    /// that cites the define (`SYNTAX.md`), and the elaborator reads a
    /// citation the same way.
    pub fn citing(&self, refs: &[String]) -> Rc<Definitions> {
        if let Some(found) = self.cited.borrow().get(refs) {
            return found.clone();
        }
        let mut made: Definitions = self
            .outside
            .iter()
            .filter(|(name, _)| {
                self.outside_labels
                    .get(*name)
                    .is_some_and(|label| refs.contains(label))
            })
            .map(|(name, d)| (name.clone(), d.clone()))
            .collect();
        made.extend(cited_defines(self.thm, self.env, &self.sorts, refs));
        let made = Rc::new(made);
        self.cited.borrow_mut().insert(refs.to_vec(), made.clone());
        made
    }

    /// What a defined name stands for in `step`'s citation (`citing`). A
    /// step citing a theorem of its own file speaks of the file's defines by
    /// name as that theorem's statement does, and reads them without citing
    /// them (`SYNTAX.md`, the one exception; the elaborator's
    /// `stated_over`).
    pub fn citing_step(&self, step: &Step) -> Rc<Definitions> {
        let item = cited_item(&step.just).map(|c| step.just.item(&c));
        self.citing_item(&step.just.refs, item.as_deref())
    }

    /// `citing` for a citation naming `refs` and citing `item`, by its full
    /// name, where it cites one: a theorem of this file brings the file's
    /// defines with it (`citing_step`).
    pub fn citing_item(&self, refs: &[String], item: Option<&str>) -> Rc<Definitions> {
        let own_file = item.is_some_and(|full| {
            full.rsplit_once('/')
                .is_some_and(|(module, _)| module == self.thm.module())
        });
        if !own_file {
            return self.citing(refs);
        }
        let mut all = refs.to_vec();
        all.extend(self.file_labels.iter().cloned());
        self.citing(&all)
    }

    /// A sentence read with what `defined` writes out (`citing`), in the
    /// standard order two trees are compared in (`matching::standard`);
    /// None where it does not read.
    pub fn read_citing(
        &self,
        sentence: &Sentence,
        defined: &Definitions,
    ) -> Option<Node> {
        self.read_as_written(sentence)
            .map(|n| standard(&expand(&n, defined), self.ctx))
    }

    /// A part that is one formula, read with what `defined` writes out;
    /// None where it is not one formula that reads, which the elaborator
    /// reports.
    pub fn read_value(&self, value: &Written, defined: &Definitions) -> Option<Node> {
        let sentence = value.sentence().ok()?;
        self.read_citing(&sentence, defined)
    }

    /// What a citation's values `v := t` say each letter stands for, all
    /// read together and with what `defined` writes out; nothing where one
    /// is not a formula that reads, which the elaborator reports.
    pub fn seed(&self, values: &Values, defined: &Definitions) -> Binding {
        let Ok(read) = values.read(self.env.g, &self.sorts) else {
            return Binding::new();
        };
        read.into_iter()
            .map(|v| (v.name, standard(&expand(&v.value, defined), self.ctx)))
            .collect()
    }

    /// What a cited line supplies (`SYNTAX.md`), each read with what
    /// `defined` writes out: each of its sentences, and where it has
    /// several, their conjunction, since "A. B" and "A and B" are one claim.
    /// A sentence that does not read is left out, as `check_formulas`
    /// reports it.
    pub fn supplied(&self, stated: &Stated, defined: &Definitions) -> Vec<Node> {
        let parts = self.said_parts(stated, Some(defined));
        let all = parts.len();
        let mut said: Vec<Node> = parts.into_iter().flatten().collect();
        if all > 1 && said.len() == all {
            said.extend(conjoined(self.env.g, said.clone()));
        }
        said
    }

    /// A tree as page text.
    pub fn print(&self, node: &Node) -> String {
        self.env.g.print(node)
    }

    /// What the lines `refs` name at `step` say, each sentence read, and
    /// each part of one that is a conjunction (`with_parts`).
    pub fn lines_say(
        &self,
        step: &Step,
        refs: &[&str],
        library: &Library,
    ) -> Vec<Node> {
        let scope = self.scope(step);
        let defined = self.citing_step(step);
        let said: Vec<Node> = refs
            .iter()
            .filter_map(|r| scope.get(*r))
            .flat_map(|written| self.supplied(written, &defined))
            .collect();
        with_parts(&said, library)
    }

    /// Every line a step's citation may name, by the reference that names
    /// it.
    pub fn scope(&self, step: &Step) -> Rc<Statements> {
        let key = (step.number.clone(), step.line);
        if let Some(found) = self.scopes.borrow().get(&key) {
            return found.clone();
        }
        let made = Rc::new(statements_in_scope(self.thm, step, self.env));
        self.scopes.borrow_mut().insert(key, made.clone());
        made
    }

    /// What a step's justification supplies and claims.
    pub fn parts(&self, step: &Step, library: &Library) -> Rc<Parts> {
        // A requires line read as a step has its step's number and its own
        // claim and reason, so those are part of what the parts depend on.
        let key = (
            step.number.clone(),
            step.claim_text(),
            step.just.text.clone(),
            step.just.refs.clone(),
            step.requires
                .iter()
                .map(|r| r.fact.text().to_string())
                .collect(),
        );
        if let Some(found) = self.parts.borrow().get(&key) {
            return found.clone();
        }
        let made = Rc::new(citation_parts(step, library, self));
        self.parts.borrow_mut().insert(key, made.clone());
        made
    }
}

/// Every line a step's citation may name, by the reference that names it.
///
/// A block's label holds inside that block only, so two sibling blocks may
/// each fix a k under the same label, and what the label says is what the
/// block around the citing step says.
pub fn statements_in_scope(thm: &Theorem, step: &Step, env: Env) -> Statements {
    // A `let` line says what its introduction asserts, and an `assume` or
    // `suppose` line its formula.
    let said = |kind, body: Written| match kind {
        Intro::Let => Stated::Introduced(Introduction::read(body)),
        _ => Stated::Written(body),
    };
    // An induction hypothesis says what its induction's claim says at the
    // letter.
    let opened = |owner: &Step, o: &crate::corpus::Opener| match o.is_hypothesis {
        true => Stated::Hypothesis(owner.claim.clone()),
        false => said(o.kind, o.body(&thm.path)),
    };
    let mut out: Statements = thm
        .steps
        .iter()
        .map(|s| (s.number.to_string(), Stated::Written(s.claim.clone())))
        .collect();
    for h in &thm.hypotheses {
        if let Some(label) = &h.label {
            out.insert(label.clone(), said(h.kind, h.body(&thm.path)));
        }
    }
    let visible = labels_in_scope(thm, step, env.scopes);
    for other in &thm.steps {
        for o in &other.openers {
            if visible.get(&o.label) == Some(&Declared::Block(o.line)) {
                out.insert(o.label.clone(), opened(other, o));
            }
        }
    }
    // A let saying what kind of number its name is says so to a line citing
    // it, besides what it names; a kind no record names is reported where
    // the lets are checked (`check_kinds`).
    for k in kinded_above(thm, step, env) {
        out.insert(
            k.label.clone(),
            Stated::Kind {
                name: Written::new(&k.name, &thm.path, k.shown.line),
                set: Written::new(&k.set, &thm.path, k.shown.line),
            },
        );
    }
    out
}

/// The lets above `step` that say what kind of number their names are, each
/// read; one whose kind no record names is left out.
pub fn kinded_above(thm: &Theorem, step: &Step, env: Env) -> Vec<Kinded> {
    thm.defines
        .iter()
        .filter(|d| d.line < step.line)
        .filter_map(|d| d.kinded(&thm.path, &env.g.members).ok().flatten())
        .collect()
}

/// A citation's seed with each name a graph given in full in the cited
/// theorem gives standing for what the citing proof calls by that name
/// (`Library::listed_names`), read in the citing proof's scope. A name the
/// citing proof does not read, or one the citation already names, is left
/// as it is.
pub fn listed_seed(
    seed: &mut Binding,
    item: &str,
    line: usize,
    known: &Known,
    library: &Library,
    defined: &Definitions,
) {
    for name in library.listed_names(item) {
        if seed.contains_key(&name) {
            continue;
        }
        let said = Written::new(&name, &known.thm.path, line);
        if let Some(got) = known.read_value(&said, defined) {
            seed.insert(name, got);
        }
    }
}

/// What a citation supplies, what it claims, and what it says its variables
/// stand for.
///
/// A defined name and the term it names are one formula where the step cites
/// the define, so all three are expanded with what it cites
/// (`Known::citing`): the facts, the claim, and the written instantiation
/// alike.
fn citation_parts(step: &Step, library: &Library, known: &Known) -> Parts {
    let scope = known.scope(step);
    let defined = known.citing_step(step);
    let read = |s: &Sentence| known.read_citing(s, &defined);
    let mut facts: Vec<Node> = Vec::new();
    for r in &step.just.refs {
        if let Some(written) = scope.get(r) {
            facts.extend(known.supplied(written, &defined));
        }
    }
    for r in &step.requires {
        facts.extend(r.fact.sentences().iter().filter_map(read));
    }
    let claims: Vec<Node> = step.claim.sentences().iter().filter_map(read).collect();
    let mut seed = known.seed(&step.just.values, &defined);
    if let Some(item) = cited_item(&step.just) {
        listed_seed(
            &mut seed,
            &step.just.item(&item),
            step.just.line,
            known,
            library,
            &defined,
        );
    }
    let mut parts = match at_a_member(step, &claims, library, &known.sorts) {
        Some((member, body)) => {
            let mut facts = facts;
            facts.push(member);
            finished(facts, vec![body], seed, library, &known.sorts)
        }
        None => finished(facts, claims, seed, library, &known.sorts),
    };
    said_once(&mut parts, &introduced(known, step), library, &known.sorts);
    if let Some(item) = cited_item(&step.just) {
        typed_seed(&mut parts, &step.just.item(&item), step, known, library);
    }
    parts
}

/// The number system each letter in scope at `step` was introduced in, by
/// the line introducing it: a `let` of the theorem or of a block around the
/// step, or an `obtain` above it in a block around it, whose claim states
/// each name's membership (`SYNTAX.md`). A later introduction of a letter
/// stands over an earlier one.
pub fn introduced(known: &Known, step: &Step) -> Introduced {
    let mut out = Introduced::new();
    for stated in &introducing(known, step) {
        for node in known.said_parts(stated, None).into_iter().flatten() {
            if let Some((letter, system)) = introduction(&node) {
                out.insert(letter, system);
            }
        }
    }
    out
}

/// The function types the lines in scope at `step` say, `v : {0, …, n} →
/// V`, read off the same introducing lines as `introduced`.
fn typed_in_scope(known: &Known, step: &Step) -> Vec<Node> {
    introducing(known, step)
        .iter()
        .flat_map(|stated| known.said_parts(stated, None).into_iter().flatten())
        .filter(|n| matches!(n.notation.as_str(), "function-type" | "one-to-one"))
        .filter(|n| n.children.len() == 3 && n.children[0].is_name())
        .collect()
}

/// The citation's seed with what the citing proof says a function of the
/// item maps between. The item's `let f : D → E` asks for nothing a line
/// writes, but where f stands for a function a line in scope types, D and E
/// are that type's sets: without them, `x ∈ D` would be met by any
/// membership of x, 5 ∈ ℕ among them, for a function on {0, …, 1}. What f
/// stands for is what the citation names it, or else what the citation
/// takes it to be.
pub fn typed_seed(
    parts: &mut Parts,
    name: &str,
    step: &Step,
    known: &Known,
    library: &Library,
) {
    let typed = library.function_types(name);
    if typed.is_empty() {
        return;
    }
    let ours = typed_in_scope(known, step);
    if ours.is_empty() {
        return;
    }
    let mut stands = parts.seed.clone();
    if let Some(groups) = library.groups(name) {
        let taken = taken(&groups, &parts.claims, &parts.facts, &parts.seed, library);
        if let Built(t) = taken {
            for (letter, value) in t.binding {
                stands.entry(letter).or_insert(value);
            }
        }
    }
    for t in &typed {
        let [f, d, e] = t.children.as_slice() else {
            continue;
        };
        let Some(v) = stands.get(&f.text).filter(|v| v.is_name()) else {
            continue;
        };
        let Some(said) = ours.iter().find(|s| s.children[0].text == v.text) else {
            continue;
        };
        for (letter, set) in [(d, &said.children[1]), (e, &said.children[2])] {
            if letter.is_name() && !parts.seed.contains_key(&letter.text) {
                parts
                    .seed
                    .insert(letter.text.clone(), standard(set, &library.ctx));
            }
        }
    }
}

/// The lines introducing what is in scope at `step`, in the order they are
/// written: a `let` of the theorem or of a block around the step, an
/// `obtain` above it in a block around it, and a naming `let` of a kind.
fn introducing(known: &Known, step: &Step) -> Vec<Stated> {
    let path = &known.thm.path;
    // What each introducing line says, by the line it is on.
    let mut said: Vec<(usize, Stated)> = known
        .thm
        .hypotheses
        .iter()
        .filter(|h| h.kind == Intro::Let)
        .map(|h| (h.line, Stated::Introduced(Introduction::read(h.body(path)))))
        .collect();
    let visible = labels_in_scope(known.thm, step, known.env.scopes);
    for other in &known.thm.steps {
        for o in &other.openers {
            if o.kind == Intro::Let
                && visible.get(&o.label) == Some(&Declared::Block(o.line))
            {
                let introduced = Introduction::read(o.body(path));
                said.push((o.line, Stated::Introduced(introduced)));
            }
        }
        let around = step.number.0.starts_with(&other.number.parent().0);
        if other.just.head.is(Method::Obtain) && other.line < step.line && around {
            said.push((other.line, Stated::Written(other.claim.clone())));
        }
    }
    for k in kinded_above(known.thm, step, known.env) {
        let kind = Stated::Kind {
            name: Written::new(&k.name, path, k.shown.line),
            set: Written::new(&k.set, path, k.shown.line),
        };
        said.push((k.shown.line, kind));
    }
    said.sort_by_key(|(line, _)| *line);
    said.into_iter().map(|(_, stated)| stated).collect()
}

/// A claim "for all k ∈ X, P" read at a member: the membership k ∈ X, which
/// the step then has as a fact, and P, which it then claims (`SYNTAX.md`, a
/// step said of every member). Which reading a citation takes is read off the
/// item, not tried: an item whose conclusions say no "for all" anywhere is
/// applied at a member, and one whose conclusions say one, as `upper-bound`
/// unfolds to one, is read as written. A define says one equation, and is
/// read at a member.
fn at_a_member(
    step: &Step,
    claims: &[Node],
    library: &Library,
    sorts: &Sorts,
) -> Option<(Node, Node)> {
    let [claim] = claims else {
        return None;
    };
    let just = &step.just;
    // A define says what its name is equal to, never a "for all", so a
    // step citing one for a "for all" is read at a member.
    if just.head != crate::corpus::Head::Define {
        if !just.head.is_item() {
            return None;
        }
        let item = library.item(&just.item(&just.head.to_string()))?;
        if item.says_for_all() {
            return None;
        }
    }
    claimed_member(claim, library, sorts)
}

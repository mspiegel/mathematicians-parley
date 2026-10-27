//! What each theorem's lines give the checks that read them.

use std::cell::{OnceCell, RefCell};
use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::IndexMap;

use super::record::{CheckedTheorem, PageReading, PartKey};
use super::structure::{labels_in_scope, Declared};
use crate::citing::{
    self, at_a_member, conjuncts_in, finished, implied_facts, introduction, said_once,
    subset_members, Introduced, Library, Parts, Taken,
};
use crate::corpus::{Intro, Kinded, Method, Step, StepNo, Theorem, Values};
use crate::formula::page::{chain_pairs, conjoined, filled, Sentence, Written};
use crate::formula::symbol::Symbol;
use crate::formula::{Node, Sorts};
use crate::matching::{
    alike, expand, standard, substitute_apart, substituted_in, Binding, Context,
    Definitions, FxIndexMap,
};
use crate::notations::{FOR_ALL, MEMBERSHIP, PLANE};
use crate::outcome::Route;
use crate::sorts::introduction::{Form, Introduction};
use crate::sorts::{citing_labels, Env, OutsideDefines, TYPING};

type PartsKey = (StepNo, String, String, Vec<String>, Vec<String>);

/// Which search of an item's groups a check asks of a step's parts
/// (`citations::searched`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Search {
    /// The group whose conclusions cover the claim (`citing::taken`).
    Takes,
    /// The group whose "there is" the step obtains through
    /// (`citing::obtained`).
    Obtains,
    /// The group whose conclusions alone cover the claim, its hypotheses
    /// not asked (`citations::concluded_alone`).
    Alone,
}

/// A search's place in `Known::searches`: the step's parts and the item's
/// groups, each by the address of the one shared copy the run keeps of it.
type SearchKey = (usize, usize, Search);

/// Every line a step's citation may name, by the reference that names it,
/// with what the line says.
pub type Statements = IndexMap<String, Stated>;

/// One thing a cited line says (`Known::says`).
#[derive(Clone, Debug)]
pub struct Said {
    /// As the checks compare it: with the defines the citation names written
    /// out, in the standard order.
    pub cited: Node,
    /// As the page writes it; a fact the line says without writing it is
    /// spelt as its rule spells it.
    pub written: Node,
    pub from: SaidFrom,
}

/// Where in a line one thing it says comes from, each counted from 0.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SaidFrom {
    /// A sentence as written.
    Sentence(usize),
    /// The conjunction of the line's several sentences.
    Whole,
    /// A part of a sentence joined by "and".
    Part { sentence: usize, part: usize },
    /// An equation of a chain the sentence writes.
    Pair(usize),
    /// The sentence, a "for all", read at a block's letter, or with `part`
    /// a part of that reading joined by "and".
    AtLetter {
        sentence: usize,
        part: Option<usize>,
    },
    /// What a membership, a range or a function's type the sentence says
    /// implies.
    Implied(usize),
    /// A subset the sentence says, as "for all" of its members.
    Members(usize),
}

impl SaidFrom {
    /// Whether the line writes it, as a sentence, a part of one, or their
    /// conjunction.
    pub fn is_written(&self) -> bool {
        matches!(
            self,
            SaidFrom::Sentence(_) | SaidFrom::Whole | SaidFrom::Part { .. }
        )
    }
}

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
    /// A line cited from inside blocks that opened with `let x ∈ X`, each
    /// below the line: what it writes, and the lets, by which a sentence
    /// "for all a ∈ X, P(a)" of it supplies P(x) as well (`SYNTAX.md`).
    InBlocks {
        line: Written,
        lets: Rc<Vec<Introduction>>,
    },
}

impl Stated {
    /// The line's text as written, for a message.
    pub fn text(&self) -> &str {
        match self {
            Stated::Written(w) => w.text(),
            Stated::Introduced(i) => i.body.text(),
            Stated::Kind { name, .. } => name.text(),
            Stated::Hypothesis(claim) => claim.text(),
            Stated::InBlocks { line, .. } => line.text(),
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
    pub ctx: &'a Context,
    /// The definitions from outside the theorem a citation may write out.
    outside: OutsideDefines,
    cited: RefCell<FxIndexMap<Vec<String>, Rc<Definitions>>>,
    scopes: RefCell<FxIndexMap<(StepNo, usize), Rc<Statements>>>,
    /// What is in scope at each place a step stands, read once for the
    /// place: a step's copies with a line taken away stand there too
    /// (`Known::in_scope`).
    in_scope: RefCell<FxIndexMap<(StepNo, usize), Rc<InScope>>>,
    parts: RefCell<FxIndexMap<PartsKey, Rc<Parts>>>,
    /// Each search a check has asked of a step's citation, which several
    /// checks ask alike: the parts and the groups are kept for the run
    /// (`parts`, `Library::groups`), so their addresses name them.
    pub(super) searches: RefCell<FxIndexMap<SearchKey, Rc<Route<Taken>>>>,
    /// The theorem's blocks and where each step stands, made once
    /// (`CheckedTheorem::of`, `Known::shape`).
    shape: std::cell::OnceCell<CheckedTheorem>,
    /// Each sentence read, by its text (`Known::parse`).
    parsed: RefCell<rustc_hash::FxHashMap<String, Node>>,
    /// Each sentence of the page read, by where it is written and its text,
    /// for the build (`CheckedTheorem::page`).
    page: RefCell<rustc_hash::FxHashMap<PartKey, Node>>,
}

impl<'a> Known<'a> {
    /// `sorts` is what the theorem's one reading settled (`checker::run`).
    pub fn new(
        thm: &'a Theorem,
        env: Env<'a>,
        sorts: Sorts,
        ctx: &'a Context,
    ) -> Known<'a> {
        Known {
            thm,
            env,
            sorts,
            ctx,
            outside: OutsideDefines::of(thm, env),
            cited: RefCell::new(FxIndexMap::default()),
            scopes: RefCell::new(FxIndexMap::default()),
            in_scope: RefCell::new(FxIndexMap::default()),
            parts: RefCell::new(FxIndexMap::default()),
            searches: RefCell::new(FxIndexMap::default()),
            shape: std::cell::OnceCell::new(),
            parsed: RefCell::new(rustc_hash::FxHashMap::default()),
            page: RefCell::new(rustc_hash::FxHashMap::default()),
        }
    }

    /// Every sentence of the page read so far, for the record the build is
    /// handed (`CheckedTheorem::page`).
    pub fn page_reading(&self) -> PageReading {
        PageReading::new(self.page.borrow().clone())
    }

    /// What each definition the theorem sees from outside it stands for,
    /// written out (`sorts::file_definitions`).
    pub fn outside_definitions(&self) -> &crate::matching::Definitions {
        &self.outside.outside
    }

    /// A sentence of the page read, kept for the build: by `parse`, and by
    /// the checks that read a define's rule with its own letters' sorts.
    /// The first reading of a sentence is the one kept.
    fn keep(&self, sentence: &Sentence, node: &Node) {
        let key = PartKey::of(sentence);
        self.page
            .borrow_mut()
            .entry(key)
            .or_insert_with(|| node.clone());
    }

    /// A sentence of the page read with sorts of its own, a define's rule
    /// with its argument's sort or its index a number, and kept for the
    /// build in place of any reading with the theorem's sorts, as this is
    /// how the line means it.
    pub fn keep_read(
        &self,
        sentence: &Sentence,
        sorts: &Sorts,
    ) -> crate::Checked<Node> {
        let node = sentence.read(self.env.g, sorts)?;
        let key = PartKey::of(sentence);
        self.page.borrow_mut().insert(key, node.clone());
        Ok(node)
    }

    /// The blocks of `thm`, the theorem this knows, and where each of its
    /// steps stands: what scopes and defines are read against.
    pub fn shape(&self) -> &CheckedTheorem {
        self.shape.get_or_init(|| CheckedTheorem::of(self.thm))
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
    fn said_parts(
        &self,
        stated: &Stated,
        defined: Option<&Definitions>,
    ) -> Vec<Option<Node>> {
        let cited = |n: Node| match defined {
            Some(d) => standard(&expand(&n, d), self.ctx),
            None => n,
        };
        match stated {
            Stated::Written(w) | Stated::InBlocks { line: w, .. } => w
                .sentences()
                .iter()
                .map(|s| self.read_as_written(s).map(cited))
                .collect(),
            Stated::Introduced(i) => match i.asserted(self.env.g, &self.sorts) {
                Ok(said) => said.into_iter().map(|n| Some(cited(n))).collect(),
                Err(_) => vec![None],
            },
            Stated::Kind { name, set } => {
                let read = |w: &Written| self.read_as_written(&w.formula().ok()?);
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
                    .formula()
                    .ok()
                    .and_then(|s| self.read_as_written(&s))
                    .and_then(|c| match (c.notation(), c.children.as_slice()) {
                        (crate::notations::FOR_ALL, [_, _, body]) => Some(body.clone()),
                        _ => None,
                    });
                vec![statement.map(cited)]
            }
        }
    }

    /// The letters a formula binds for itself: each a binder holds, by what
    /// the grammar declares it holds (`for all c ∈ ℕ`, `{c ∈ A : …}`,
    /// `Σ(c = 1 to n)`).
    pub fn bound(&self, node: &Node) -> BTreeSet<String> {
        let binders = self.env.g.binders();
        let mut out = BTreeSet::new();
        for n in node.walk() {
            let Some(binds) = binders.get(&n.notation()) else {
                continue;
            };
            for &at in &binds.held {
                if let Some(letter) = n.children.get(at).filter(|l| l.is_name()) {
                    out.insert(letter.text.to_string());
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

    /// The sentence read with its defined names kept, as a message prints
    /// it; None where it does not read, which `check_formulas` reports.
    pub fn read_as_written(&self, sentence: &Sentence) -> Option<Node> {
        self.parse(sentence).ok()
    }

    /// The sentence parsed with the theorem's sorts, or why it does not
    /// read. The sorts are the theorem's throughout, so a sentence's text
    /// decides its tree, and each text is parsed once; a reading that fails
    /// is not kept, as its problem says where the sentence is written.
    pub fn parse(&self, sentence: &Sentence) -> crate::Checked<Node> {
        let Some(text) = sentence.deciding_text() else {
            let node = sentence.read(self.env.g, &self.sorts)?;
            self.keep(sentence, &node);
            return Ok(node);
        };
        let cached = self.parsed.borrow().get(text).cloned();
        let node = match cached {
            Some(node) => node,
            None => {
                let node = sentence.read(self.env.g, &self.sorts)?;
                self.parsed
                    .borrow_mut()
                    .insert(text.to_string(), node.clone());
                node
            }
        };
        self.keep(sentence, &node);
        Ok(node)
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

    /// Whether `aim` is `start` with one side of `left = right` put for the
    /// other (`matching::substituted_in`), each read in the standard order
    /// as `alike` reads it.
    pub fn substituted(
        &self,
        start: &Node,
        aim: &Node,
        left: &Node,
        right: &Node,
    ) -> bool {
        let s = |n: &Node| standard(n, self.ctx);
        substituted_in(&s(start), &s(aim), &s(left), &s(right), self.ctx)
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
        let made = Rc::new(self.outside.citing(self.thm, self.env, &self.sorts, refs));
        self.cited.borrow_mut().insert(refs.to_vec(), made.clone());
        made
    }

    /// What a defined name stands for in `step`'s citation (`citing`). A
    /// step citing a theorem of its own file speaks of the defines above it
    /// by name as that theorem's statement does, and reads them without
    /// citing them (`sorts::stated_over`).
    pub fn citing_step(&self, step: &Step) -> Rc<Definitions> {
        let item = step.just.cited_item().map(|c| step.just.item(&c));
        self.citing_item(&step.just.refs, item.as_deref())
    }

    /// `citing` for a citation naming `refs` and citing `item`, by its full
    /// name, where it cites one: a theorem of this file brings the defines
    /// it is stated over with it (`citing_step`).
    pub fn citing_item(&self, refs: &[String], item: Option<&str>) -> Rc<Definitions> {
        self.citing(&citing_labels(self.thm, self.env.scopes, refs, item))
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

    /// The membership a step said of every member in one line gives its
    /// member, k ∈ X of "for all k ∈ X, P", read as its citations are
    /// (`citing::claimed_member`); "for all X ⊆ A" gives X ⊆ A. None for a
    /// claim of another form or of more than one sentence.
    pub fn step_member(&self, step: &Step) -> Option<Node> {
        let defined = self.citing_step(step);
        let [sentence] = step.claim.sentences().try_into().ok()?;
        let whole = self.read_citing(&sentence, &defined)?;
        crate::citing::claimed_member(&whole, self.env.g).map(|(member, _)| member)
    }

    /// A part that is one formula, read with what `defined` writes out;
    /// None where it is not one formula that reads, which the elaborator
    /// reports.
    pub fn read_value(&self, value: &Written, defined: &Definitions) -> Option<Node> {
        let sentence = value.formula().ok()?;
        self.read_citing(&sentence, defined)
    }

    /// What a citation's values `v := t` say each letter stands for, all
    /// read together, each as its place in the cited item wants it
    /// (`letters`, its sorts), and with what `defined` writes out; nothing
    /// where one is not a formula that reads, which the elaborator reports.
    pub fn seed(
        &self,
        values: &Values,
        defined: &Definitions,
        letters: Option<&Sorts>,
    ) -> Binding {
        let Ok(read) = values.read_wanted(self.env.g, &self.sorts, letters) else {
            return Binding::new();
        };
        read.into_iter()
            .map(|v| {
                (
                    Symbol::of(&v.name),
                    standard(&expand(&v.value, defined), self.ctx),
                )
            })
            .collect()
    }

    /// Everything a cited line says (`SYNTAX.md`, What a cited line says):
    /// each sentence, and where it has several their conjunction; the parts
    /// of a sentence joined by "and"; every equation of a chain; a "for all"
    /// read at the letter of a block around the step; and what a membership
    /// implies, a range's bounds and a function's wider types among it.
    /// Each is given as written and as `defined` writes it out, with where
    /// in the line it comes from. A sentence that does not read is left
    /// out, as `check_formulas` reports it.
    pub fn says(&self, stated: &Stated, defined: &Definitions) -> Vec<Said> {
        let sentences: Vec<Option<Node>> = self.said_parts(stated, None);
        let mut written: Vec<(Node, SaidFrom)> = Vec::new();
        let read: Vec<&Node> = sentences.iter().flatten().collect();
        for (i, sentence) in sentences.iter().enumerate() {
            let Some(sentence) = sentence else {
                continue;
            };
            self.say_of(sentence, i, SaidFrom::Sentence(i), &mut written);
            for at in
                self.at_block_letters(stated, std::slice::from_ref(sentence), None)
            {
                let from = SaidFrom::AtLetter {
                    sentence: i,
                    part: None,
                };
                self.say_of(&at, i, from, &mut written);
            }
            // A "for all" that is one "and" part of the sentence is read at
            // the block's letter as one written as its own sentence is:
            // `q is a polynomial and (for all x ∈ ℂ, …)` says the "for all"
            // at the block's x.
            let parts = conjuncts_in(sentence, self.ctx, self.env.g);
            if parts.len() > 1 {
                for (j, part) in parts.iter().enumerate() {
                    for at in
                        self.at_block_letters(stated, std::slice::from_ref(part), None)
                    {
                        let from = SaidFrom::AtLetter {
                            sentence: i,
                            part: Some(j),
                        };
                        self.say_of(&at, i, from, &mut written);
                    }
                }
            }
            // A subset's members said as a "for all" are read at a block's
            // letter as a written one is.
            let members: Vec<Node> = written
                .iter()
                .filter(|(_, from)| *from == SaidFrom::Members(i))
                .map(|(n, _)| n.clone())
                .collect();
            for at in self.at_block_letters(stated, &members, None) {
                written.push((at, SaidFrom::Members(i)));
            }
        }
        if sentences.len() > 1 && read.len() == sentences.len() {
            let all: Vec<Node> = read.into_iter().cloned().collect();
            if let Some(whole) = conjoined(self.env.g, all) {
                written.push((whole, SaidFrom::Whole));
            }
        }
        let mut out: Vec<Said> = Vec::new();
        for (node, from) in written {
            let cited = self.as_cited(&node, defined);
            if out.iter().any(|s| self.alike(&s.cited, &cited)) {
                continue;
            }
            out.push(Said {
                cited,
                written: node,
                from,
            });
        }
        out
    }

    /// What one sentence of a line, or its reading at a block's letter,
    /// says: itself as `from`, its "and" parts and a chain's equations, and
    /// what each of those implies (`implied_facts`).
    fn say_of(
        &self,
        sentence: &Node,
        i: usize,
        from: SaidFrom,
        out: &mut Vec<(Node, SaidFrom)>,
    ) {
        let mut here: Vec<(Node, SaidFrom)> = vec![(sentence.clone(), from)];
        let parts = conjuncts_in(sentence, self.ctx, self.env.g);
        if parts.len() > 1 {
            for (j, part) in parts.into_iter().enumerate() {
                let tag = match from {
                    SaidFrom::AtLetter { .. } => SaidFrom::AtLetter {
                        sentence: i,
                        part: Some(j),
                    },
                    _ => SaidFrom::Part {
                        sentence: i,
                        part: j,
                    },
                };
                here.push((part, tag));
            }
        }
        let pairs: Vec<Node> = here
            .iter()
            .filter_map(|(n, _)| chain_pairs(self.env.g, n))
            .flatten()
            .collect();
        here.extend(pairs.into_iter().map(|p| (p, SaidFrom::Pair(i))));
        let members: Vec<Node> = here
            .iter()
            .filter_map(|(n, _)| subset_members(n, self.env, &self.sorts))
            .collect();
        here.extend(members.into_iter().map(|m| (m, SaidFrom::Members(i))));
        let implied: Vec<Node> = here
            .iter()
            .flat_map(|(n, _)| implied_facts(n, self.env, &self.sorts))
            .collect();
        here.extend(implied.into_iter().map(|n| (n, SaidFrom::Implied(i))));
        out.extend(here);
    }

    /// Whether every sentence of a line reads; one that does not is
    /// `check_formulas`'s to report, and a check of what the line says is
    /// then not judged.
    pub fn reads(&self, stated: &Stated) -> bool {
        self.said_parts(stated, None).iter().all(Option::is_some)
    }

    /// What a line writes, for `join` (`SYNTAX.md`, What a cited line says),
    /// as the page has it: each sentence and their conjunction, and the
    /// parts of a sentence joined by "and", a chain's equations between
    /// neighbouring terms among them; and a "for all" of it read at a
    /// block's letter, which is the line as the block reads it. Neither what
    /// it implies nor a chain's other equations.
    pub fn writes(&self, stated: &Stated, defined: &Definitions) -> Vec<Node> {
        self.says(stated, defined)
            .into_iter()
            .filter(|s| {
                !matches!(
                    s.from,
                    SaidFrom::Pair(_) | SaidFrom::Implied(_) | SaidFrom::Members(_)
                )
            })
            .map(|s| s.written)
            .collect()
    }

    /// What a line writes (`writes`) and a subset it writes as "for all" of
    /// its members, as the page has it: what an item's search may be handed
    /// by the line beyond what the search reads of it itself, a function's
    /// type or a term at every point (`citations::does_other_work`).
    pub fn writes_with_members(
        &self,
        stated: &Stated,
        defined: &Definitions,
    ) -> Vec<Node> {
        self.says(stated, defined)
            .into_iter()
            .filter(|s| !matches!(s.from, SaidFrom::Pair(_) | SaidFrom::Implied(_)))
            .map(|s| s.written)
            .collect()
    }

    /// The line's sentences as the page writes them, for a check of how the
    /// page is written: the letters a sentence binds, the applications it
    /// writes. A sentence that does not read is left out.
    pub fn sentences(&self, stated: &Stated) -> Vec<Node> {
        self.said_parts(stated, None)
            .into_iter()
            .flatten()
            .collect()
    }

    /// What a cited line says (`says`) for a route that reads what a
    /// membership implies itself: an item's facts are finished with it
    /// (`citing::finished`), and a method takes it as an automatic fact
    /// (`METHODS.md`), so a fact the line only implies is left out here and
    /// is not counted as a line the step adds.
    pub fn supplied(&self, stated: &Stated, defined: &Definitions) -> Vec<Node> {
        self.says(stated, defined)
            .into_iter()
            .filter(|s| !matches!(s.from, SaidFrom::Implied(_)))
            .map(|s| s.cited)
            .collect()
    }

    /// What the "for all" sentences `said` of a line say at the letter of a
    /// block around the citing step (`SYNTAX.md`): "for all a ∈ X, P(a)" in a
    /// block that opened with `let x ∈ X` supplies P(x). The lets are read
    /// as `said` was, with `defined` written out or not; where two give
    /// letters of X the citation says neither.
    fn at_block_letters(
        &self,
        stated: &Stated,
        said: &[Node],
        defined: Option<&Definitions>,
    ) -> Vec<Node> {
        let Stated::InBlocks { lets, .. } = stated else {
            return Vec::new();
        };
        let members: Vec<Node> = lets
            .iter()
            .flat_map(|i| {
                let introduced = Stated::Introduced(i.clone());
                self.said_parts(&introduced, defined)
            })
            .flatten()
            .filter(|m| m.notation() == MEMBERSHIP && m.children.len() == 2)
            .collect();
        let mut out = Vec::new();
        for sentence in said {
            let [bound, domain, body] = sentence.children.as_slice() else {
                continue;
            };
            if sentence.notation() != FOR_ALL {
                continue;
            }
            let letters: Vec<&Node> = members
                .iter()
                .filter(|m| self.alike(&m.children[1], domain))
                .map(|m| &m.children[0])
                .collect();
            let [letter] = letters.as_slice() else {
                continue;
            };
            let mut put = Binding::new();
            put.insert(bound.text, (*letter).clone());
            out.push(substitute_apart(body, &put, self.ctx));
        }
        out
    }

    /// A tree as page text.
    pub fn print(&self, node: &Node) -> String {
        self.env.g.print(node)
    }

    /// Everything the lines `refs` name at `step` say (`says`), as the
    /// checks of `step` compare it.
    pub fn lines_say(&self, step: &Step, refs: &[&str]) -> Vec<Node> {
        let scope = self.scope(step);
        let defined = self.citing_step(step);
        refs.iter()
            .filter_map(|r| scope.get(*r))
            .flat_map(|written| self.says(written, &defined))
            .map(|s| s.cited)
            .collect()
    }

    /// Every line a step's citation may name, by the reference that names
    /// it.
    pub fn scope(&self, step: &Step) -> Rc<Statements> {
        let key = (step.number.clone(), step.line);
        if let Some(found) = self.scopes.borrow().get(&key) {
            return found.clone();
        }
        let made = Rc::new(statements_in_scope(self.thm, self.shape(), step, self.env));
        self.scopes.borrow_mut().insert(key, made.clone());
        made
    }

    /// What is in scope where `step` stands: the lines introducing it, and
    /// what is read off them as it is first asked for. Which lines a step
    /// names does not change what is in scope at its place.
    pub fn in_scope(&self, step: &Step) -> Rc<InScope> {
        let key = (step.number.clone(), step.line);
        if let Some(found) = self.in_scope.borrow().get(&key) {
            return found.clone();
        }
        let made = Rc::new(InScope {
            introducing: introducing(self, step),
            introduced: OnceCell::new(),
            points: OnceCell::new(),
            typed: OnceCell::new(),
        });
        self.in_scope.borrow_mut().insert(key, made.clone());
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
pub fn statements_in_scope(
    thm: &Theorem,
    shape: &CheckedTheorem,
    step: &Step,
    env: Env,
) -> Statements {
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
    // A number written twice is `check_numbering`'s to report; a citation
    // of it reads the one written nearest above the citing step.
    let visible = labels_in_scope(thm, shape, step, env.scopes);
    let lets = block_lets(thm, &visible);
    let mut out: Statements = Statements::new();
    for s in &thm.steps {
        let key = s.number.to_string();
        if s.line <= step.line || !out.contains_key(&key) {
            out.insert(key, in_blocks(s.claim.clone(), s.line, &lets));
        }
    }
    for h in &thm.hypotheses {
        if let Some(label) = &h.label {
            let stated = match h.kind {
                Intro::Let => said(h.kind, h.body(&thm.path)),
                _ => in_blocks(h.body(&thm.path), h.line, &lets),
            };
            out.insert(label.clone(), stated);
        }
    }
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
    for k in kinded_above(thm, shape, step, env) {
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

/// The `let x ∈ X` lines opening the blocks around a step, by the line each
/// stands on.
fn block_lets(
    thm: &Theorem,
    visible: &IndexMap<String, Declared>,
) -> Vec<(usize, Introduction)> {
    thm.steps
        .iter()
        .flat_map(|s| &s.openers)
        .filter(|o| o.kind == Intro::Let)
        .filter(|o| visible.get(&o.label) == Some(&Declared::Block(o.line)))
        .map(|o| (o.line, Introduction::read(o.body(&thm.path))))
        .filter(|(_, i)| matches!(i.form, Form::Member))
        .collect()
}

/// What a line written on `line` says to a citation: its text, read at the
/// letters of the lets below it that open blocks around the citing step
/// (`Stated::InBlocks`).
fn in_blocks(written: Written, line: usize, lets: &[(usize, Introduction)]) -> Stated {
    let below: Vec<Introduction> = lets
        .iter()
        .filter(|(at, _)| *at > line)
        .map(|(_, i)| i.clone())
        .collect();
    if below.is_empty() {
        return Stated::Written(written);
    }
    Stated::InBlocks {
        line: written,
        lets: Rc::new(below),
    }
}

/// The lets above `step` that say what kind of number their names are, each
/// read; one whose kind no record names is left out.
pub fn kinded_above(
    thm: &Theorem,
    shape: &CheckedTheorem,
    step: &Step,
    env: Env,
) -> Vec<Kinded> {
    thm.defines
        .iter()
        .enumerate()
        .filter(|(i, _)| shape.define_in_scope(thm, *i, step))
        .filter_map(|(_, d)| d.kinded(&thm.path, &env.g.members).ok().flatten())
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
        if seed.contains_key(name.as_str()) {
            continue;
        }
        let said = Written::new(&name, &known.thm.path, line);
        if let Some(got) = known.read_value(&said, defined) {
            seed.insert(Symbol::of(&name), got);
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
    let letters = step
        .just
        .cited_item()
        .and_then(|item| library.item_sorts(&step.just.item(&item)));
    let mut seed = known.seed(&step.just.values, &defined, letters);
    if let Some(item) = step.just.cited_item() {
        listed_seed(
            &mut seed,
            &step.just.item(&item),
            step.just.line,
            known,
            library,
            &defined,
        );
    }
    let mut letters = introduced(known, step);
    let mut parts = match at_a_member(step, &claims, library) {
        Some((member, body)) => {
            // A step said of every member introduces the member as the same
            // step's block would by its `let`: j of "for all j ∈ {1, …, m}"
            // is in ℕ, the system the range is in (`SYNTAX.md`).
            if let Some((letter, system)) =
                crate::citing::introduction(&member, &letters)
            {
                letters.insert(letter, system);
            }
            let mut facts = facts;
            facts.push(member);
            finished(facts, vec![body], seed, library, &known.sorts)
        }
        None => finished(facts, claims, seed, library, &known.sorts),
    };
    let typed = typed_in_scope(known, step);
    let points = points_introduced(known, step);
    said_once(&mut parts, &letters, &points, &typed, library, &known.sorts);
    if let Some(item) = step.just.cited_item() {
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
    let here = known.in_scope(step);
    here.introduced
        .get_or_init(|| introduced_by(known, &here.introducing))
        .clone()
}

/// `introduced`, from the introducing lines in scope.
fn introduced_by(known: &Known, introducing: &[Stated]) -> Introduced {
    let mut out = Introduced::new();
    for stated in introducing {
        for node in known.said_parts(stated, None).into_iter().flatten() {
            if let Some((letter, system)) = introduction(&node, &out) {
                out.insert(letter, system);
            }
        }
    }
    out
}

/// The letters in scope at `step` that the page introduces as points, by
/// the line introducing each: `let A be a point`, or a line saying A ∈ 𝔼²,
/// as `let A ∈ 𝔼²` or an `obtain` does. Each is in the plane by that line,
/// said once (`citing::said_once`); a letter whose sort only its use gives
/// is not.
pub fn points_introduced(known: &Known, step: &Step) -> BTreeSet<String> {
    let here = known.in_scope(step);
    here.points
        .get_or_init(|| points_by(known, &here.introducing))
        .clone()
}

/// `points_introduced`, from the introducing lines in scope.
fn points_by(known: &Known, introducing: &[Stated]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for stated in introducing {
        if let Stated::Introduced(i) = stated {
            if let Form::Point(name) = &i.form {
                out.insert(name.clone());
            }
        }
        for node in known.said_parts(stated, None).into_iter().flatten() {
            if let [letter, set] = node.children.as_slice() {
                if node.notation() == MEMBERSHIP
                    && set.notation() == PLANE
                    && letter.is_name()
                {
                    out.insert(letter.text.to_string());
                }
            }
        }
    }
    out
}

/// The sums a step writes that the page says are numbers once, by their
/// terms at every index (`citing::sum_said_once`): those in its claim, its
/// requires lines and the lines it and they cite, as written
/// (`CheckedTheorem::said_sums`).
pub fn sums_said_once(known: &Known, step: &Step) -> Vec<Node> {
    let letters = introduced(known, step);
    let typed = typed_in_scope(known, step);
    let scope = known.scope(step);
    let mut written: Vec<Node> = Vec::new();
    for w in std::iter::once(&step.claim).chain(step.requires.iter().map(|r| &r.fact)) {
        written.extend(
            w.sentences()
                .iter()
                .filter_map(|s| known.read_as_written(s)),
        );
    }
    // The rows of an inequalities step write what it combines, the first a
    // line it cites written out.
    if let Some(Ok(rows)) = crate::corpus::proof::rows(&step.just, &known.thm.path) {
        for row in &rows {
            written.extend(
                row.formula
                    .sentences()
                    .iter()
                    .filter_map(|s| known.read_as_written(s)),
            );
        }
    }
    let refs = step
        .just
        .refs
        .iter()
        .chain(step.requires.iter().flat_map(|r| r.refs()));
    for r in refs {
        if let Some(stated) = scope.get(r) {
            written.extend(known.writes(stated, &known.citing_step(step)));
        }
    }
    // A sum under a binder of the line, Σ(k = 1 to m) for all m, speaks of
    // a letter the scope does not hold, and no step combines it as it is.
    let in_scope = |sum: &Node| {
        let bound: BTreeSet<String> = sum
            .walk()
            .iter()
            .filter(|n| n.notation() == crate::notations::SUM)
            .filter_map(|n| n.children.first().map(|i| i.text.to_string()))
            .collect();
        sum.names().iter().all(|n| {
            bound.contains(n)
                || letters.contains_key(n)
                || typed.iter().any(|t| t.children[0].text == *n)
        })
    };
    let mut out: Vec<Node> = Vec::new();
    for node in written.iter().flat_map(|n| n.walk()).filter(in_scope) {
        let said = citing::sum_said_once(
            &node,
            crate::rules::System::C,
            &letters,
            &typed,
            known.ctx,
        );
        if said {
            out.push(node);
        }
    }
    out
}

/// The function types the lines in scope at `step` say, `v : {0, …, n} →
/// V`, read off the same introducing lines as `introduced`.
pub fn typed_in_scope(known: &Known, step: &Step) -> Vec<Node> {
    let here = known.in_scope(step);
    here.typed
        .get_or_init(|| typed_by(known, &here.introducing))
        .clone()
}

/// `typed_in_scope`, from the introducing lines in scope.
fn typed_by(known: &Known, introducing: &[Stated]) -> Vec<Node> {
    introducing
        .iter()
        .flat_map(|stated| known.said_parts(stated, None).into_iter().flatten())
        .filter(|n| TYPING.contains(&n.notation()))
        .filter(|n| n.children.len() == 3 && n.children[0].is_name())
        .collect()
}

/// The citation's seed with what the citing proof says a function of the
/// item maps between (`citing::typed_seed`), from the function types the
/// lines in scope at `step` say.
pub fn typed_seed(
    parts: &mut Parts,
    name: &str,
    step: &Step,
    known: &Known,
    library: &Library,
) {
    citing::typed_seed(parts, name, &typed_in_scope(known, step), library);
}

/// What is in scope at one place a step stands (`Known::in_scope`): the
/// introducing lines, and what `introduced`, `points_introduced` and
/// `typed_in_scope` read off them, each read when first asked for.
pub struct InScope {
    introducing: Vec<Stated>,
    introduced: OnceCell<Introduced>,
    points: OnceCell<BTreeSet<String>>,
    typed: OnceCell<Vec<Node>>,
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
    let visible = labels_in_scope(known.thm, known.shape(), step, known.env.scopes);
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
    for k in kinded_above(known.thm, known.shape(), step, known.env) {
        let kind = Stated::Kind {
            name: Written::new(&k.name, path, k.shown.line),
            set: Written::new(&k.set, path, k.shown.line),
        };
        said.push((k.shown.line, kind));
    }
    said.sort_by_key(|(line, _)| *line);
    said.into_iter().map(|(_, stated)| stated).collect()
}

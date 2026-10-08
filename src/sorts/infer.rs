//! The one reading of a text's lines that says what sort each name is.
//!
//! `READERS.md` says a set's sort says what it holds and the page never
//! writes it, and `GRAMMAR.md` says how it is read: each notation's `sort`
//! field in `corpus/db/notation.records` relates the sorts of its holes, and
//! a name takes the most general sort the text allows. This module is that
//! reading: sort terms, the one field's syntax, unification, and inference
//! over a parse tree, a line at a time. The checker decides what to read and
//! reports what does not fit.
//!
//! A sort term is `number`, `point`, `formula`, `group-element`, `set of S`,
//! `property of S`, `function from S to S`, or a variable. A variable is
//! *flexible* when the text may still say what it is, and *rigid* when it
//! stands for "any sort" a statement declared — `let X be a set` makes X a
//! set of a rigid sort, which its own statement and proof may not narrow,
//! since the statement is claimed of every sort. A cited statement's sorts
//! are copied flexible at each use, so each citing step takes the sort it
//! needs.
//!
//! Unifying two sorts that do not fit gives back a decline saying why. That
//! is a value: the checker reports it, and nothing tries another reading
//! after it.

use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use crate::corpus::{define_parts, DefineParts, Intro, Method, Record, Step, Theorem};
use crate::formula::{parse_here, Node, Sort, Sorts, Whole};
use crate::matching::Defined;
use crate::outcome::{At, Built, Decline, Declined, Route};
use crate::regex;
use crate::sorts::{
    define_sorts, element_re, file_definitions, graph_line, group_re, let_formula,
    property_re, sentences, set_or_point_re, unlabel, Env,
};
use crate::text::repr;

regex!(OBTAINS_RE, r"^obtain\s+([^:]+?)(?::|\s+from)");

/// The names an `obtain` justification obtains, as written before its colon
/// or its `from`.
pub fn obtains(text: &str) -> Option<String> {
    OBTAINS_RE.captures(text).map(|m| m[1].to_string())
}

/// A sort that is not a set, property or function of something.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Atom {
    Number,
    Point,
    Formula,
    GroupElement,
}

impl Atom {
    fn parse(word: &str) -> Option<Atom> {
        Some(match word {
            "number" => Atom::Number,
            "point" => Atom::Point,
            "formula" => Atom::Formula,
            "group-element" => Atom::GroupElement,
            _ => return None,
        })
    }
}

pub type VarId = usize;

/// A sort as the reading holds it: an atom, a set, property or function of
/// sorts, or a variable the text may still settle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SortTerm {
    Atom(Atom),
    Set(Box<SortTerm>),
    Property(Box<SortTerm>),
    Function(Box<SortTerm>, Box<SortTerm>),
    Var(VarId),
}

impl SortTerm {
    fn set(k: SortTerm) -> SortTerm {
        SortTerm::Set(Box::new(k))
    }
}

pub const NUMBER: SortTerm = SortTerm::Atom(Atom::Number);
pub const POINT: SortTerm = SortTerm::Atom(Atom::Point);
pub const FORMULA: SortTerm = SortTerm::Atom(Atom::Formula);
pub const GROUP_ELEMENT: SortTerm = SortTerm::Atom(Atom::GroupElement);

struct VarData {
    bound: Option<SortTerm>,
    rigid: bool,
    said: String,
}

/// Every sort variable of a run, and what each has been fixed to.
///
/// One store serves every reader that may share variables: a cited
/// statement's sorts are copied into the reader of the proof citing it.
#[derive(Default)]
pub struct Store {
    vars: Vec<VarData>,
}

impl Store {
    /// A sort not yet known.
    pub fn var(&mut self) -> SortTerm {
        self.var_said(false, "")
    }

    fn var_said(&mut self, rigid: bool, said: &str) -> SortTerm {
        self.vars.push(VarData {
            bound: None,
            rigid,
            said: said.to_string(),
        });
        SortTerm::Var(self.vars.len() - 1)
    }

    /// The sort with every fixed variable at its head followed.
    pub fn find(&self, k: &SortTerm) -> SortTerm {
        let mut k = k.clone();
        while let SortTerm::Var(v) = k {
            match &self.vars[v].bound {
                Some(next) => k = next.clone(),
                None => break,
            }
        }
        k
    }

    /// A sort as a reader would say it.
    pub fn show(&self, k: &SortTerm) -> String {
        match self.find(k) {
            SortTerm::Var(v) => {
                let d = &self.vars[v];
                if d.rigid {
                    if d.said.is_empty() {
                        "any sort".to_string()
                    } else {
                        format!("any sort ({})", d.said)
                    }
                } else {
                    "a sort not yet settled".to_string()
                }
            }
            SortTerm::Atom(Atom::Number) => "a number".into(),
            SortTerm::Atom(Atom::Point) => "a point".into(),
            SortTerm::Atom(Atom::Formula) => "a statement".into(),
            SortTerm::Atom(Atom::GroupElement) => "a group element".into(),
            SortTerm::Set(k) => format!("a set of {}", self.plural(&k)),
            SortTerm::Property(k) => format!("a property of {}", self.plural(&k)),
            SortTerm::Function(a, b) => {
                format!("a function from {} to {}", self.plural(&a), self.plural(&b))
            }
        }
    }

    fn plural(&self, k: &SortTerm) -> String {
        let said = self.show(k);
        for (one, many) in [
            ("a number", "numbers"),
            ("a point", "points"),
            ("a group element", "group elements"),
            ("a statement", "statements"),
            ("a set of", "sets of"),
            ("a property of", "properties of"),
            ("a function from", "functions from"),
        ] {
            if let Some(rest) = said.strip_prefix(one) {
                return format!("{many}{rest}");
            }
        }
        format!("things of {said}")
    }

    fn occurs(&self, v: VarId, k: &SortTerm) -> bool {
        match self.find(k) {
            SortTerm::Var(w) => w == v,
            SortTerm::Atom(_) => false,
            SortTerm::Set(c) | SortTerm::Property(c) => self.occurs(v, &c),
            SortTerm::Function(a, b) => self.occurs(v, &a) || self.occurs(v, &b),
        }
    }

    /// Make the two sorts one, or decline saying why they cannot be.
    pub fn unify(&mut self, a: &SortTerm, b: &SortTerm) -> Route<()> {
        let (a, b) = (self.find(a), self.find(b));
        if let (SortTerm::Var(x), SortTerm::Var(y)) = (&a, &b) {
            if x == y {
                return Built(());
            }
        }
        if let SortTerm::Var(v) = a {
            if !self.vars[v].rigid {
                if self.occurs(v, &b) {
                    return Route::no(format!(
                        "{} would have to hold itself",
                        self.show(&b)
                    ));
                }
                self.vars[v].bound = Some(b);
                return Built(());
            }
        }
        if let SortTerm::Var(v) = b {
            if !self.vars[v].rigid {
                return self.unify(&b, &a);
            }
        }
        if matches!(a, SortTerm::Var(_)) || matches!(b, SortTerm::Var(_)) {
            let (rigid, other) = if matches!(a, SortTerm::Var(_)) {
                (&a, &b)
            } else {
                (&b, &a)
            };
            return Route::no(format!(
                "{} is declared of any sort, and here it would have to be {}",
                self.show(rigid),
                self.show(other)
            ));
        }
        let pairs: Vec<(SortTerm, SortTerm)> = match (&a, &b) {
            (SortTerm::Atom(x), SortTerm::Atom(y)) if x == y => Vec::new(),
            (SortTerm::Set(x), SortTerm::Set(y))
            | (SortTerm::Property(x), SortTerm::Property(y)) => {
                vec![((**x).clone(), (**y).clone())]
            }
            (SortTerm::Function(x1, x2), SortTerm::Function(y1, y2)) => vec![
                ((**x1).clone(), (**y1).clone()),
                ((**x2).clone(), (**y2).clone()),
            ],
            _ => {
                return Route::no(format!(
                    "{} where {} is wanted",
                    self.show(&a),
                    self.show(&b)
                ))
            }
        };
        for (x, y) in pairs {
            if self.unify(&x, &y).is_declined() {
                return Route::no(format!(
                    "{} where {} is wanted",
                    self.show(&a),
                    self.show(&b)
                ));
            }
        }
        Built(())
    }

    /// A sort with its variables replaced by fresh flexible ones.
    ///
    /// The same fresh one stands wherever the same variable stood, so what a
    /// cited statement relates stays related in the copy.
    pub fn copy(
        &mut self,
        k: &SortTerm,
        seen: &mut IndexMap<VarId, SortTerm>,
    ) -> SortTerm {
        match self.find(k) {
            SortTerm::Var(v) => {
                if let Some(fresh) = seen.get(&v) {
                    return fresh.clone();
                }
                let fresh = self.var();
                seen.insert(v, fresh.clone());
                fresh
            }
            SortTerm::Atom(a) => SortTerm::Atom(a),
            SortTerm::Set(c) => SortTerm::set(self.copy(&c, seen)),
            SortTerm::Property(c) => SortTerm::Property(Box::new(self.copy(&c, seen))),
            SortTerm::Function(a, b) => {
                let a = self.copy(&a, seen);
                let b = self.copy(&b, seen);
                SortTerm::Function(Box::new(a), Box::new(b))
            }
        }
    }

    fn make_rigid(&mut self, k: &SortTerm, name: &str) {
        match self.find(k) {
            SortTerm::Var(v) => {
                self.vars[v].rigid = true;
                if self.vars[v].said.is_empty() {
                    self.vars[v].said = name.to_string();
                }
            }
            SortTerm::Atom(_) => {}
            SortTerm::Set(c) | SortTerm::Property(c) => self.make_rigid(&c, name),
            SortTerm::Function(a, b) => {
                self.make_rigid(&a, name);
                self.make_rigid(&b, name);
            }
        }
    }
}

/// A sort term as the sort it settles, in full, or None where it settles
/// none: a statement, or a sort left open.
pub fn sort(store: &Store, k: &SortTerm) -> Option<Sort> {
    fn whole(store: &Store, k: &SortTerm) -> Whole {
        match store.find(k) {
            SortTerm::Var(_) => Whole::Open,
            SortTerm::Atom(Atom::Number) => Whole::Number,
            SortTerm::Atom(Atom::Point) => Whole::Point,
            SortTerm::Atom(Atom::Formula) => Whole::Formula,
            SortTerm::Atom(Atom::GroupElement) => Whole::GroupElement,
            SortTerm::Set(c) => Whole::Set(Rc::new(whole(store, &c))),
            SortTerm::Property(c) => Whole::Property(Rc::new(whole(store, &c))),
            SortTerm::Function(a, b) => {
                Whole::Function(Rc::new(whole(store, &a)), Rc::new(whole(store, &b)))
            }
        }
    }
    Sort::whole(whole(store, k))
}

// ------------------------------------------------------------ the field

/// A sort as a notation's `sort` field writes it, with its variables still
/// named.
#[derive(Clone, Debug)]
enum Template {
    Atom(Atom),
    Set(Box<Template>),
    Property(Box<Template>),
    Function(Box<Template>, Box<Template>),
    Var(String),
}

impl Template {
    /// The coarse class of a sort, as `Whole::category` gives it for a sort
    /// that is fixed, and `any` for one that is a variable.
    fn category(&self) -> &'static str {
        match self {
            Template::Atom(Atom::Number) => "number",
            Template::Atom(Atom::Point) => "point",
            Template::Atom(Atom::Formula) => "formula",
            Template::Atom(Atom::GroupElement) => "group-element",
            Template::Set(inner) => match &**inner {
                Template::Atom(Atom::GroupElement) => "group-set",
                Template::Set(_) => "set-of-sets",
                _ => "set",
            },
            Template::Property(_) => "property",
            Template::Function(..) => "function",
            Template::Var(_) => "any",
        }
    }
}

/// A `sort` field: the sort of each hole and of what the notation produces,
/// related by the variables they share.
#[derive(Clone, Debug)]
pub struct Signature {
    parts: Vec<Template>,
    result: Template,
}

impl Signature {
    pub fn holes(&self) -> usize {
        self.parts.len()
    }

    /// The category of each hole and of the result: the coarse class the
    /// parser tells readings apart by.
    pub fn categories(&self) -> (Vec<&'static str>, &'static str) {
        let holes = self.parts.iter().map(Template::category).collect();
        (holes, self.result.category())
    }

    /// Each (element, set) pair of holes the signature relates as a thing
    /// and a set holding things of its sort: `α` and `set of α`, as a
    /// membership's are.
    pub fn members(&self) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        for (i, a) in self.parts.iter().enumerate() {
            let Template::Var(x) = a else { continue };
            for (j, b) in self.parts.iter().enumerate() {
                if let Template::Set(inner) = b {
                    if matches!(&**inner, Template::Var(y) if y == x) {
                        out.push((i, j));
                    }
                }
            }
        }
        out
    }

    /// Fresh hole sorts and result sort, with fresh variables.
    pub fn fresh(&self, store: &mut Store) -> (Vec<SortTerm>, SortTerm) {
        let mut names: IndexMap<String, SortTerm> = IndexMap::new();
        let holes = self
            .parts
            .iter()
            .map(|t| instance(t, &mut names, store))
            .collect();
        let result = instance(&self.result, &mut names, store);
        (holes, result)
    }

    /// What a node of this signature produces, where the sorts of what fills
    /// its holes settle a result the signature leaves to a variable:
    /// application's β, from the function in its first hole, so cos(x) is a
    /// number and |cos(x)| an absolute value. None where they do not, or
    /// where they disagree with the signature, which the hole check reports.
    pub fn settled(&self, filled: &[&Sort]) -> Option<Sort> {
        let mut store = Store::default();
        let (holes, result) = self.fresh(&mut store);
        for (hole, sort) in holes.iter().zip(filled) {
            let Some(whole) = sort.full() else { continue };
            let said = term_of(whole, &mut store);
            if store.unify(hole, &said).is_declined() {
                return None;
            }
        }
        if matches!(store.find(&result), SortTerm::Var(_)) {
            return None;
        }
        sort(&store, &result)
    }
}

/// A sort in full as a term, its open parts fresh variables.
fn term_of(whole: &Whole, store: &mut Store) -> SortTerm {
    match whole {
        Whole::Number => NUMBER,
        Whole::Point => POINT,
        Whole::Formula => FORMULA,
        Whole::GroupElement => GROUP_ELEMENT,
        Whole::Set(c) => SortTerm::set(term_of(c, store)),
        Whole::Property(c) => SortTerm::Property(Box::new(term_of(c, store))),
        Whole::Function(a, b) => {
            let a = term_of(a, store);
            let b = term_of(b, store);
            SortTerm::Function(Box::new(a), Box::new(b))
        }
        Whole::Open => store.var(),
    }
}

fn instance(
    t: &Template,
    names: &mut IndexMap<String, SortTerm>,
    store: &mut Store,
) -> SortTerm {
    match t {
        Template::Atom(a) => SortTerm::Atom(*a),
        Template::Var(name) => {
            if let Some(k) = names.get(name) {
                return k.clone();
            }
            let k = store.var();
            names.insert(name.clone(), k.clone());
            k
        }
        Template::Set(c) => SortTerm::set(instance(c, names, store)),
        Template::Property(c) => {
            SortTerm::Property(Box::new(instance(c, names, store)))
        }
        Template::Function(a, b) => {
            let a = instance(a, names, store);
            let b = instance(b, names, store);
            SortTerm::Function(Box::new(a), Box::new(b))
        }
    }
}

regex!(
    TOKEN,
    r"group-element|set of|property of|function from|to|number|point|formula|[α-ω]"
);

/// A `sort` field, or a decline saying what in it does not read.
/// `check_notation` reports that; everything else skips a notation whose
/// field is one.
pub fn signature(text: &str) -> Route<Signature> {
    let Some((holes_text, result_text)) = text.split_once('→') else {
        return Route::no(format!("{} has no `→` before what it produces", repr(text)));
    };
    let holes: Vec<&str> = holes_text
        .split(',')
        .map(str::trim)
        .filter(|h| !h.is_empty())
        .collect();
    let mut templates = Vec::new();
    for h in holes.iter().copied().chain([str::trim(result_text)]) {
        match read_template(h) {
            Built(t) => templates.push(t),
            Declined(d) => return Declined(d),
        }
    }
    let result = templates.pop().unwrap();
    Built(Signature {
        parts: templates,
        result,
    })
}

/// A library function's `sort` line, `number, number → number`, as the one
/// sort the reading gives a function: a function from its first argument to
/// a function from the next, and so on to its value, which is how the
/// application patterns take their arguments. It has no holes of its own.
pub fn function_signature(text: &str) -> Route<Signature> {
    let said = match signature(text) {
        Built(said) => said,
        Declined(d) => return Declined(d),
    };
    let result = said
        .parts
        .into_iter()
        .rev()
        .fold(said.result, |value, argument| {
            Template::Function(Box::new(argument), Box::new(value))
        });
    Built(Signature {
        parts: Vec::new(),
        result,
    })
}

/// The sort a library function's name has in a formula, read off its `sort`
/// line; None where the line does not read.
pub fn function_sort(text: &str) -> Option<Sort> {
    let Built(said) = function_signature(text) else {
        return None;
    };
    let mut store = Store::default();
    let (_, value) = said.fresh(&mut store);
    sort(&store, &value)
}

fn read_template(text: &str) -> Route<Template> {
    let tokens: Vec<&str> = TOKEN.find_iter(text).map(|m| m.as_str()).collect();
    if tokens.concat().replace(' ', "") != text.replace(' ', "") {
        return Route::no(format!("{} is not a sort", repr(text)));
    }
    let (tree, rest) = match term(&tokens) {
        Built(got) => got,
        Declined(d) => return Declined(d),
    };
    if !rest.is_empty() {
        return Route::no(format!(
            "{} has {} left over",
            repr(text),
            repr(&rest.join(" "))
        ));
    }
    Built(tree)
}

fn term<'t>(tokens: &'t [&'t str]) -> Route<(Template, &'t [&'t str])> {
    let Some((&head, rest)) = tokens.split_first() else {
        return Route::no("a sort is missing");
    };
    if let Some(atom) = Atom::parse(head) {
        return Built((Template::Atom(atom), rest));
    }
    if head == "set of" || head == "property of" {
        let (inner, rest) = match term(rest) {
            Built(got) => got,
            Declined(d) => return Declined(d),
        };
        let made = if head == "set of" {
            Template::Set(Box::new(inner))
        } else {
            Template::Property(Box::new(inner))
        };
        return Built((made, rest));
    }
    if head == "function from" {
        let (a, rest) = match term(rest) {
            Built(got) => got,
            Declined(d) => return Declined(d),
        };
        if rest.first() != Some(&"to") {
            return Route::no("`function from` wants `to`");
        }
        let (b, rest) = match term(&rest[1..]) {
            Built(got) => got,
            Declined(d) => return Declined(d),
        };
        return Built((Template::Function(Box::new(a), Box::new(b)), rest));
    }
    if head == "to" {
        return Route::no("`to` stands without `function from`");
    }
    Built((Template::Var(head.to_string()), rest))
}

// ------------------------------------------------------------ reading

/// What does not fit: where, what, and why.
#[derive(Clone, Debug)]
pub struct Clash {
    pub line: At,
    pub what: String,
    pub why: String,
}

/// The sorts of one statement or proof, read in the order it is written.
///
/// `env` maps a name to its sort; a `let` shadows what came before, since a
/// block may use a letter an earlier one did. What does not fit is kept in
/// `clashes`.
pub struct Reader {
    pub env: IndexMap<String, SortTerm>,
    pub clashes: Vec<Clash>,
    /// Names declared of any sort, not yet fixed.
    declared: Vec<String>,
    notations: Rc<NotationSorts>,
    /// What the statement's `ε, δ range over ℝ` lines say, which a line is
    /// parsed with as it is with the sorts.
    pub ranges: IndexMap<String, String>,
    /// The library functions in scope: those the file imports, or every one
    /// in a library record.
    pub imported: IndexSet<String>,
}

/// The library functions in scope in a theorem: those its file imports.
fn imported_in(thm: &Theorem, env: Env) -> IndexSet<String> {
    env.scopes
        .get(thm.scope)
        .map(|s| s.function_names())
        .unwrap_or_default()
}

/// The library functions in scope in a library record: every one, since the
/// library sees itself.
fn every_function(env: Env) -> IndexSet<String> {
    env.g.functions.keys().cloned().collect()
}

/// Each letter a statement's range lines name, with the set it belongs to.
pub fn ranges_of(ranges: &[crate::corpus::Range]) -> IndexMap<String, String> {
    let mut out = IndexMap::new();
    for r in ranges {
        for name in &r.names {
            out.entry(name.clone()).or_insert_with(|| r.set.clone());
        }
    }
    out
}

/// What every notation says about sorts: the signature its `sort` field
/// declares, and which of its holes bind a variable.
///
/// It depends on the grammar alone, so it is read once per grammar
/// (`Grammar::notation_sorts`) and every reader shares it; each use of a
/// signature takes fresh variables of its own (`Signature::fresh`).
pub struct NotationSorts {
    signatures: IndexMap<String, Rc<Signature>>,
    bound: IndexMap<String, IndexSet<usize>>,
    /// The sort of each function the library declares, by its name.
    functions: IndexMap<String, Rc<Signature>>,
}

impl NotationSorts {
    pub fn read(g: &crate::formula::Grammar) -> NotationSorts {
        let mut signatures: IndexMap<String, Rc<Signature>> = IndexMap::new();
        let mut bound: IndexMap<String, IndexSet<usize>> = IndexMap::new();
        for n in &g.notations {
            let key = n.key().to_string();
            let Some(said) = &n.sort else { continue };
            if said.is_empty() {
                continue;
            }
            let Built(made) = signature(said) else {
                continue;
            };
            let made = Rc::new(made);
            signatures
                .entry(key.clone())
                .or_insert_with(|| made.clone());
            signatures.entry(n.name.clone()).or_insert(made);
            if !n.holes.is_empty() {
                let entry = bound.entry(key).or_default();
                for (i, h) in n.holes.iter().enumerate() {
                    if h == "variable" {
                        entry.insert(i);
                    }
                }
            }
        }
        let mut functions: IndexMap<String, Rc<Signature>> = IndexMap::new();
        for (name, f) in &g.functions {
            if let Built(said) = function_signature(&f.sort) {
                functions.insert(name.clone(), Rc::new(said));
            }
        }
        NotationSorts {
            signatures,
            bound,
            functions,
        }
    }

    /// The signature a node of this notation reads by, where it has one.
    pub fn signature(&self, notation: &str) -> Option<&Signature> {
        self.signatures.get(notation).map(|s| &**s)
    }
}

impl Reader {
    pub fn new(env: Env) -> Reader {
        Reader {
            env: IndexMap::new(),
            clashes: Vec::new(),
            declared: Vec::new(),
            notations: env.g.notation_sorts(),
            ranges: IndexMap::new(),
            imported: IndexSet::new(),
        }
    }

    /// The sort of every name the lines read so far settle: what the next
    /// line is parsed with.
    pub fn sorts(&self, store: &Store) -> Sorts {
        crate::sorts::settled(self, store)
    }

    fn of_name(&mut self, name: &str, store: &mut Store) -> SortTerm {
        if let Some(k) = self.env.get(name) {
            return k.clone();
        }
        // A name the lines never gave a sort, which the library declares as a
        // function, has the library's sort, in a copy of its own as a
        // notation's signature is.
        let library = self
            .imported
            .contains(name)
            .then(|| self.notations.functions.get(name))
            .flatten();
        let k = match library {
            Some(said) => said.fresh(store).1,
            None => store.var(),
        };
        self.env.insert(name.to_string(), k.clone());
        k
    }

    fn clash(&mut self, line: At, what: impl Into<String>, why: &Decline) {
        self.clashes.push(Clash {
            line,
            what: what.into(),
            why: why.reason(),
        });
    }

    /// The sort of a parse tree, noting every clash inside it.
    pub fn sort_of(
        &mut self,
        node: &Node,
        line: At,
        local: &IndexMap<String, SortTerm>,
        store: &mut Store,
    ) -> SortTerm {
        if node.is_name() {
            if let Some(k) = local.get(&node.text) {
                return k.clone();
            }
            return self.of_name(&node.text, store);
        }
        if node.notation == "numeral" {
            return NUMBER;
        }
        let notations = Rc::clone(&self.notations);
        let (holes, out) = match notations.signatures.get(&node.notation) {
            Some(make) if make.holes() == node.children.len() => make.fresh(store),
            // A notation whose `sort` is missing or does not read, which
            // `check_notation` reports: nothing is known of its holes.
            _ => {
                let holes = node.children.iter().map(|_| store.var()).collect();
                (holes, store.var())
            }
        };
        let mut inner = local.clone();
        if let Some(indices) = notations.bound.get(&node.notation) {
            for &i in indices {
                if i < node.children.len() && node.children[i].is_name() {
                    let v = store.var();
                    inner.insert(node.children[i].text.clone(), v);
                }
            }
        }
        for (child, want) in node.children.iter().zip(holes.iter()) {
            let got = self.sort_of(child, line, &inner, store);
            if let Declined(said) = store.unify(&got, want) {
                let what = if child.text.is_empty() {
                    child.notation.clone()
                } else {
                    child.text.clone()
                };
                self.clash(line, what, &said);
            }
        }
        out
    }

    pub fn claim(&mut self, node: &Node, line: At, store: &mut Store) {
        let k = self.sort_of(node, line, &IndexMap::new(), store);
        if let Declined(said) = store.unify(&k, &FORMULA) {
            self.clash(line, "the line", &said);
        }
    }

    /// Make what the declared names' sorts still leave open rigid.
    ///
    /// Called once the lines declaring them are read: the statement's
    /// hypotheses and conclusion, or a block's opening lines. What they
    /// related is related; what they left open is "any sort" from here on,
    /// and a proof that narrows it is proving less than it claims.
    pub fn fix_declared(&mut self, store: &mut Store) {
        for name in std::mem::take(&mut self.declared) {
            if let Some(k) = self.env.get(&name).cloned() {
                store.make_rigid(&k, &name);
            }
        }
    }
}

// The name a `let` line introduces, a name before its own line is read:
// `let n ∈ ℕ`, `let f : A → B`, and `let p be a polynomial`, which reads
// "p is a polynomial". A letter that is also a constant, `i`, is the name
// throughout the line that introduces it.
regex!(INTRODUCED_NAME, r"^([^\s∈∉:]+)(?:\s*(?:∈|∉|:)|\s+is\s)");

/// What a `let` line says a name is, into the reader's sorts.
///
/// `be a set` and `be an element` declare a thing of any sort. The lines
/// declaring it may still relate it to another — `X ∖ {a}` makes a the sort
/// of what X holds — so the sort is left free here and noted in `declared`,
/// and `fix_declared` fixes it once the statement or the block's opening
/// lines are read. The rest name a thing whose sort the text fixes, and the
/// line is read as a claim.
pub fn introduce(
    reader: &mut Reader,
    body: &str,
    line: At,
    env: Env,
    store: &mut Store,
) {
    let body = str::trim(&unlabel(body)).to_string();
    // A graph, its vertices and its edges: three sets, of things of no sort
    // the line says. Vertices and edges are whatever names the theorem gives
    // them; a graph given in full names each of them, of the sort its set
    // holds.
    if let Some(line) = graph_line(&body) {
        let graph = store.var_said(false, &line.graph);
        reader.env.insert(line.graph.clone(), SortTerm::set(graph));
        reader.declared.push(line.graph.clone());
        for (set, listed) in [
            (&line.vertices, line.listed.as_ref().map(|l| &l.vertices)),
            (&line.edges, line.listed.as_ref().map(|l| &l.edges)),
        ] {
            let held = store.var_said(false, set);
            reader.env.insert(set.clone(), SortTerm::set(held.clone()));
            reader.declared.push(set.clone());
            for name in listed.into_iter().flatten() {
                reader.env.insert(name.clone(), held.clone());
                reader.declared.push(name.clone());
            }
        }
        return;
    }
    // A group is a set of group elements, and its identity is one of them.
    if let Some(m) = group_re().captures(&body) {
        reader
            .env
            .insert(m["group"].to_string(), SortTerm::set(GROUP_ELEMENT));
        reader.env.insert(m["identity"].to_string(), GROUP_ELEMENT);
        return;
    }
    if let Some(m) = set_or_point_re().captures(&body) {
        let name = m[1].to_string();
        if &m[2] == "set" {
            let v = store.var_said(false, &name);
            reader.env.insert(name.clone(), SortTerm::set(v));
            reader.declared.push(name);
        } else {
            reader.env.insert(name, POINT);
        }
        return;
    }
    if let Some(m) = element_re().captures(&body) {
        let name = m[1].to_string();
        let v = store.var_said(false, &name);
        reader.env.insert(name.clone(), v);
        reader.declared.push(name);
        return;
    }
    if let Some(m) = property_re().captures(&body) {
        let of = store.var();
        reader
            .env
            .insert(m[1].to_string(), SortTerm::Property(Box::new(of.clone())));
        let domain = reader.of_name(&m[2], store);
        if let Declined(said) = store.unify(&domain, &SortTerm::set(of)) {
            reader.clash(line, &m[2], &said);
        }
        return;
    }
    let body = let_formula(&body);
    if let Some(m) = INTRODUCED_NAME.captures(&body) {
        let v = store.var();
        reader.env.insert(m[1].to_string(), v);
    }
    claim_text(reader, &body, line, env, store);
}

/// Every sentence of a line, read as a claim.
///
/// One that does not parse is `check_formulas`'s to report, and is passed
/// over here.
pub fn claim_text(
    reader: &mut Reader,
    text: &str,
    line: At,
    env: Env,
    store: &mut Store,
) {
    for sentence in sentences(text) {
        let Ok(node) = parse_here(&sentence, env.g, &reader.sorts(store)) else {
            continue;
        };
        reader.claim(&node, line, store);
    }
}

/// An item's sorts, read from its own lines in the order they are written.
///
/// A record keeps the keyword of a hypothesis in the field name where a
/// proof line keeps it in the text, and has no steps.
pub fn read_record(record: &Record, env: Env, store: &mut Store) -> Reader {
    let mut reader = Reader::new(env);
    reader.ranges = ranges_of(&record.ranges);
    reader.imported = every_function(env);
    for h in &record.hypotheses {
        if h.kind == Intro::Let {
            introduce(&mut reader, &h.text, h.line.into(), env, store);
        } else {
            let text = str::trim(&unlabel(&h.text)).to_string();
            claim_text(&mut reader, &text, h.line.into(), env, store);
        }
    }
    for (text, no) in &record.conclusions {
        claim_text(&mut reader, text, (*no).into(), env, store);
    }
    reader
}

/// What a proved theorem's statement says its names are: its hypotheses and
/// its conclusion, without the proof beneath, which is what a citation of it
/// reads.
///
/// A cited statement is read on its own, and each citation takes its own
/// copy of what it says (`Store::copy`), so the sorts a statement relates
/// stay related and nothing one citation fixes reaches another.
pub fn read_statement(thm: &Theorem, env: Env, store: &mut Store) -> Reader {
    let mut reader = Reader::new(env);
    reader.ranges = ranges_of(&thm.ranges);
    reader.imported = imported_in(thm, env);
    for h in &thm.hypotheses {
        let body = str::trim(&unlabel(&h.text[h.kind.as_str().len()..])).to_string();
        if h.kind == Intro::Let {
            introduce(&mut reader, &body, h.line.into(), env, store);
        } else {
            claim_text(&mut reader, &body, h.line.into(), env, store);
        }
    }
    claim_text(&mut reader, &thm.conclusion, thm.line.into(), env, store);
    reader
}

/// An item's sorts as its `let` lines alone say them: what the item
/// declares, before its assumptions and conclusions use anything.
pub fn read_lets(record: &Record, env: Env, store: &mut Store) -> Reader {
    let mut reader = Reader::new(env);
    reader.ranges = ranges_of(&record.ranges);
    reader.imported = every_function(env);
    for h in record.hypotheses.iter().filter(|h| h.kind == Intro::Let) {
        introduce(&mut reader, &h.text, h.line.into(), env, store);
    }
    reader
}

/// The sorts of the sequences a define by recursion gives: each takes a
/// number, the index, and gives what its value at 0 is, which each rule at
/// k + 1 must give too. Every name is in scope in every rule, since a rule
/// may name any of the sequences at k.
/// The sort of a function taking `taken` one at a time and giving `gives`:
/// a function of two is a function from the first to a function from the
/// second, as `application-to-two` reads one.
fn curried(taken: Vec<SortTerm>, gives: SortTerm) -> SortTerm {
    taken.into_iter().rev().fold(gives, |inner, one| {
        SortTerm::Function(Box::new(one), Box::new(inner))
    })
}

fn recursion_sorts(
    reader: &mut Reader,
    said: &crate::corpus::Recursion,
    line: At,
    env: Env,
    store: &mut Store,
) {
    let mut gives: IndexMap<String, SortTerm> = IndexMap::new();
    for name in &said.names {
        gives.insert(name.clone(), store.var());
    }
    for name in &said.names {
        reader.env.insert(
            name.clone(),
            SortTerm::Function(Box::new(NUMBER), Box::new(gives[name].clone())),
        );
    }
    let mut local_sorts = reader.sorts(store);
    local_sorts.insert(said.index.clone(), Sort::of("number"));
    let mut at_step = IndexMap::new();
    at_step.insert(said.index.clone(), NUMBER);
    for (rules, local) in [(&said.start, IndexMap::new()), (&said.step, at_step)] {
        for (name, rule) in rules {
            let Ok(tree) = parse_here(rule, env.g, &local_sorts) else {
                continue; // `check_formulas` says it does not read
            };
            let got = reader.sort_of(&tree, line, &local, store);
            if let Declined(fits) = store.unify(&got, &gives[name]) {
                reader.clash(line, name, &fits);
            }
        }
    }
}

/// What a step's citations are fitted against, called after its claim is
/// read.
pub type Cite<'c> = &'c mut dyn FnMut(&mut Reader, &mut Store, &Step);

/// A theorem's sorts, read in the order its lines are written.
///
/// A `let` shadows an earlier name, since blocks reuse letters. What the
/// statement or a block's opening lines declared of any sort is fixed where
/// the proof under them begins. `cite` is called after each step's claim is
/// read, for whoever fits its citations.
pub fn read_theorem(
    thm: &Theorem,
    env: Env,
    store: &mut Store,
    mut cite: Option<Cite>,
) -> Reader {
    let mut reader = Reader::new(env);
    reader.ranges = ranges_of(&thm.ranges);
    reader.imported = imported_in(thm, env);
    // What the theorem sees from outside it has its sort before its first
    // line, read from the rule written out where it was defined.
    for (name, made) in file_definitions(thm, env) {
        let term = match made {
            Defined::Rule(rule) => {
                let mut local = IndexMap::new();
                let mut taken = Vec::new();
                for p in &rule.params {
                    let one = store.var();
                    local.insert(p.name.clone(), one.clone());
                    taken.push(one);
                }
                let gives = reader.sort_of(&rule.body, thm.line.into(), &local, store);
                curried(taken, gives)
            }
            Defined::Term(t) => {
                reader.sort_of(&t, thm.line.into(), &IndexMap::new(), store)
            }
        };
        reader.env.insert(name, term);
    }
    enum Event<'t> {
        Let(&'t str),
        Said(String),
        Define(&'t str),
        Claim(&'t Step),
    }
    // Each line, where it stands, and whether reading it first fixes what
    // was declared of any sort: a define, a claim and a requires line do,
    // since the proof has begun by then.
    let mut events: Vec<(At, bool, Event)> = Vec::new();
    fn opening(intro: Intro, text: &str) -> Event<'_> {
        let rest = &text[intro.as_str().len()..];
        if intro == Intro::Let {
            Event::Let(rest)
        } else {
            Event::Said(str::trim(&unlabel(rest)).to_string())
        }
    }
    for h in &thm.hypotheses {
        events.push((h.line.into(), false, opening(h.kind, &h.text)));
    }
    // The conclusion is the statement's last line, so it may still relate
    // what the hypotheses declared of any sort.
    let after = thm
        .hypotheses
        .iter()
        .map(|h| h.line)
        .max()
        .unwrap_or(thm.line);
    events.push((
        At::after(after),
        false,
        Event::Said(str::trim(&unlabel(&thm.conclusion)).to_string()),
    ));
    for d in &thm.defines {
        events.push((d.line.into(), true, Event::Define(&d.text)));
    }
    for step in &thm.steps {
        for o in &step.openers {
            events.push((o.line.into(), false, opening(o.kind, &o.text)));
        }
        events.push((step.line.into(), true, Event::Claim(step)));
        for r in &step.requires {
            events.push((
                r.line.into(),
                true,
                Event::Said(str::trim(&unlabel(&r.fact)).to_string()),
            ));
        }
    }
    events.sort_by_key(|e| e.0);
    for (no, fixes, event) in &events {
        let no = *no;
        if *fixes {
            reader.fix_declared(store);
        }
        match event {
            Event::Let(text) => introduce(&mut reader, text, no, env, store),
            Event::Said(text) => claim_text(&mut reader, text, no, env, store),
            Event::Define(text) => {
                let Built(said) = define_parts(text) else {
                    continue;
                };
                let said = match said {
                    DefineParts::Recursion(r) => {
                        recursion_sorts(&mut reader, &r, no, env, store);
                        continue;
                    }
                    DefineParts::One(d) => d,
                };
                let sorts = reader.sorts(store);
                if said.params.is_empty() {
                    let Ok(tree) = parse_here(&said.body, env.g, &sorts) else {
                        continue;
                    };
                    let k = reader.sort_of(&tree, no, &IndexMap::new(), store);
                    reader.env.insert(said.name.clone(), k);
                    continue;
                }
                // A function: what each domain holds goes in, one argument
                // at a time, what its rule gives comes out, and the
                // parameters are its rule's own names.
                let local_sorts = define_sorts(&said, &sorts);
                let mut local = IndexMap::new();
                let mut taken = Vec::new();
                let mut read = true;
                for p in &said.params {
                    let Ok(over_tree) = parse_here(&p.domain, env.g, &local_sorts)
                    else {
                        read = false;
                        break;
                    };
                    let over = reader.sort_of(&over_tree, no, &IndexMap::new(), store);
                    let one = store.var();
                    if let Declined(said_of) =
                        store.unify(&over, &SortTerm::set(one.clone()))
                    {
                        reader.clash(no, p.domain.clone(), &said_of);
                    }
                    local.insert(p.name.clone(), one.clone());
                    taken.push(one);
                }
                if !read {
                    continue;
                }
                let Ok(body_tree) = parse_here(&said.body, env.g, &local_sorts) else {
                    continue;
                };
                let gives = reader.sort_of(&body_tree, no, &local, store);
                reader.env.insert(said.name.clone(), curried(taken, gives));
            }
            Event::Claim(step) => {
                let obtained = if step.just.head.is(Method::Obtain) {
                    obtains(&step.just.text)
                } else {
                    None
                };
                if let Some(names) = obtained {
                    for name in split_names(str::trim(&names)) {
                        let v = store.var();
                        reader.env.insert(name.to_string(), v);
                    }
                }
                claim_text(&mut reader, &step.claim_text(), no, env, store);
                if let Some(cite) = cite.as_mut() {
                    cite(&mut reader, store, step);
                }
            }
        }
    }
    reader
}

regex!(NAME_COMMA, r"\s*,\s*");

/// `re.split(r'\s*,\s*', text)`.
fn split_names(text: &str) -> Vec<&str> {
    NAME_COMMA.split(text).collect()
}

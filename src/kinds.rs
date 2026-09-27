//! Kinds: what a set holds, read off how a text uses its names.
//!
//! `READERS.md` says a set has the kind of what it holds and the page never
//! writes it, and `GRAMMAR.md` says how it is read: each notation's `kinds`
//! field in `db/notation.records` relates the kinds of its holes, and a name
//! takes the most general kind the text allows. This module is that reading:
//! kind terms, the one field's syntax, unification, and inference over a
//! parse tree. The checker decides what to read and reports what does not
//! fit.
//!
//! A kind is `number`, `point`, `formula`, `set of K`, `property of K`,
//! `function from K to K`, or a variable. A variable is *flexible* when the
//! text may still say what it is, and *rigid* when it stands for "any kind"
//! a statement declared — `let X be a set` makes X a set of a rigid kind,
//! which its own statement and proof may not narrow, since the statement is
//! claimed of every kind. A cited statement's kinds are copied flexible at
//! each use, so each citing step takes the kind it needs.
//!
//! Unifying two kinds that do not fit gives back a decline saying why. That
//! is a value: the checker reports it, and nothing tries another reading
//! after it.

use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use crate::corpus::{define_parts, DefineParts, Intro, Method, Record, Step, Theorem};
use crate::formula::{parse_here, Node, Sort, Sorts};
use crate::matching::Defined;
use crate::outcome::{At, Built, Decline, Declined, Route};
use crate::regex;
use crate::sorts::{
    define_sorts, element_re, file_definitions, group_re, kind_re, let_formula,
    property_re, sentences, unlabel, Env,
};
use crate::text::{pystr, repr};

regex!(OBTAINS_RE, r"^obtain\s+([^:]+?)(?::|\s+from)");

/// The names an `obtain` justification obtains, as written before its colon
/// or its `from`.
pub fn obtains(text: &str) -> Option<String> {
    OBTAINS_RE.captures(text).map(|m| m[1].to_string())
}

/// A kind that is not a set of something.
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

/// A kind: an atom, a set, property or function of kinds, or a variable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
    Atom(Atom),
    Set(Box<Kind>),
    Property(Box<Kind>),
    Function(Box<Kind>, Box<Kind>),
    Var(VarId),
}

impl Kind {
    fn set(k: Kind) -> Kind {
        Kind::Set(Box::new(k))
    }
}

pub const NUMBER: Kind = Kind::Atom(Atom::Number);
pub const POINT: Kind = Kind::Atom(Atom::Point);
pub const FORMULA: Kind = Kind::Atom(Atom::Formula);
pub const GROUP_ELEMENT: Kind = Kind::Atom(Atom::GroupElement);

struct VarData {
    bound: Option<Kind>,
    rigid: bool,
    said: String,
}

/// Every kind variable of a run, and what each has been fixed to.
///
/// One store serves every reader that may share variables: a cited
/// statement's kinds are copied into the reader of the proof citing it.
#[derive(Default)]
pub struct Store {
    vars: Vec<VarData>,
}

impl Store {
    /// A kind not yet known.
    pub fn var(&mut self) -> Kind {
        self.var_said(false, "")
    }

    fn var_said(&mut self, rigid: bool, said: &str) -> Kind {
        self.vars.push(VarData {
            bound: None,
            rigid,
            said: said.to_string(),
        });
        Kind::Var(self.vars.len() - 1)
    }

    /// The kind with every fixed variable at its head followed.
    pub fn find(&self, k: &Kind) -> Kind {
        let mut k = k.clone();
        while let Kind::Var(v) = k {
            match &self.vars[v].bound {
                Some(next) => k = next.clone(),
                None => break,
            }
        }
        k
    }

    /// A kind as a reader would say it.
    pub fn show(&self, k: &Kind) -> String {
        match self.find(k) {
            Kind::Var(v) => {
                let d = &self.vars[v];
                if d.rigid {
                    if d.said.is_empty() {
                        "any kind".to_string()
                    } else {
                        format!("any kind ({})", d.said)
                    }
                } else {
                    "a kind not yet fixed".to_string()
                }
            }
            Kind::Atom(Atom::Number) => "a number".into(),
            Kind::Atom(Atom::Point) => "a point".into(),
            Kind::Atom(Atom::Formula) => "a statement".into(),
            Kind::Atom(Atom::GroupElement) => "a group element".into(),
            Kind::Set(k) => format!("a set of {}", self.plural(&k)),
            Kind::Property(k) => format!("a property of {}", self.plural(&k)),
            Kind::Function(a, b) => {
                format!("a function from {} to {}", self.plural(&a), self.plural(&b))
            }
        }
    }

    fn plural(&self, k: &Kind) -> String {
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

    fn occurs(&self, v: VarId, k: &Kind) -> bool {
        match self.find(k) {
            Kind::Var(w) => w == v,
            Kind::Atom(_) => false,
            Kind::Set(c) | Kind::Property(c) => self.occurs(v, &c),
            Kind::Function(a, b) => self.occurs(v, &a) || self.occurs(v, &b),
        }
    }

    /// Make the two kinds one, or decline saying why they cannot be.
    pub fn unify(&mut self, a: &Kind, b: &Kind) -> Route<()> {
        let (a, b) = (self.find(a), self.find(b));
        if let (Kind::Var(x), Kind::Var(y)) = (&a, &b) {
            if x == y {
                return Built(());
            }
        }
        if let Kind::Var(v) = a {
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
        if let Kind::Var(v) = b {
            if !self.vars[v].rigid {
                return self.unify(&b, &a);
            }
        }
        if matches!(a, Kind::Var(_)) || matches!(b, Kind::Var(_)) {
            let (rigid, other) = if matches!(a, Kind::Var(_)) {
                (&a, &b)
            } else {
                (&b, &a)
            };
            return Route::no(format!(
                "{} is declared of any kind, and here it would have to be {}",
                self.show(rigid),
                self.show(other)
            ));
        }
        let pairs: Vec<(Kind, Kind)> = match (&a, &b) {
            (Kind::Atom(x), Kind::Atom(y)) if x == y => Vec::new(),
            (Kind::Set(x), Kind::Set(y)) | (Kind::Property(x), Kind::Property(y)) => {
                vec![((**x).clone(), (**y).clone())]
            }
            (Kind::Function(x1, x2), Kind::Function(y1, y2)) => vec![
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

    /// A kind with its variables replaced by fresh flexible ones.
    ///
    /// The same fresh one stands wherever the same variable stood, so what a
    /// cited statement relates stays related in the copy.
    pub fn copy(&mut self, k: &Kind, seen: &mut IndexMap<VarId, Kind>) -> Kind {
        match self.find(k) {
            Kind::Var(v) => {
                if let Some(fresh) = seen.get(&v) {
                    return fresh.clone();
                }
                let fresh = self.var();
                seen.insert(v, fresh.clone());
                fresh
            }
            Kind::Atom(a) => Kind::Atom(a),
            Kind::Set(c) => Kind::set(self.copy(&c, seen)),
            Kind::Property(c) => Kind::Property(Box::new(self.copy(&c, seen))),
            Kind::Function(a, b) => {
                let a = self.copy(&a, seen);
                let b = self.copy(&b, seen);
                Kind::Function(Box::new(a), Box::new(b))
            }
        }
    }

    fn make_rigid(&mut self, k: &Kind, name: &str) {
        match self.find(k) {
            Kind::Var(v) => {
                self.vars[v].rigid = true;
                if self.vars[v].said.is_empty() {
                    self.vars[v].said = name.to_string();
                }
            }
            Kind::Atom(_) => {}
            Kind::Set(c) | Kind::Property(c) => self.make_rigid(&c, name),
            Kind::Function(a, b) => {
                self.make_rigid(&a, name);
                self.make_rigid(&b, name);
            }
        }
    }
}

/// The flat sort a kind settles, or None where it settles none.
pub fn sort_of(store: &Store, k: &Kind) -> Option<&'static str> {
    match store.find(k) {
        Kind::Var(_) => None,
        Kind::Set(inner) => {
            // A set of a group's elements is a group's set, which says what
            // it holds; a set of sets says what it holds too: `|Y|` for Y in
            // it is a size.
            match store.find(&inner) {
                Kind::Atom(Atom::GroupElement) => Some("group-set"),
                Kind::Set(_) => Some("set-of-sets"),
                _ => Some("set"),
            }
        }
        Kind::Atom(Atom::Number) => Some("number"),
        Kind::Atom(Atom::Point) => Some("point"),
        Kind::Atom(Atom::GroupElement) => Some("group-element"),
        Kind::Atom(Atom::Formula) => None,
        Kind::Function(..) => Some("function"),
        Kind::Property(_) => Some("property"),
    }
}

// ------------------------------------------------------------ the field

/// A kind as a `kinds` field writes it, with its variables still named.
#[derive(Clone, Debug)]
enum Template {
    Atom(Atom),
    Set(Box<Template>),
    Property(Box<Template>),
    Function(Box<Template>, Box<Template>),
    Var(String),
}

/// A `kinds` field: the kind of each hole and of what the notation produces,
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

    /// Fresh hole kinds and result kind, with fresh variables.
    pub fn fresh(&self, store: &mut Store) -> (Vec<Kind>, Kind) {
        let mut names: IndexMap<String, Kind> = IndexMap::new();
        let holes = self
            .parts
            .iter()
            .map(|t| instance(t, &mut names, store))
            .collect();
        let result = instance(&self.result, &mut names, store);
        (holes, result)
    }
}

fn instance(
    t: &Template,
    names: &mut IndexMap<String, Kind>,
    store: &mut Store,
) -> Kind {
    match t {
        Template::Atom(a) => Kind::Atom(*a),
        Template::Var(name) => {
            if let Some(k) = names.get(name) {
                return k.clone();
            }
            let k = store.var();
            names.insert(name.clone(), k.clone());
            k
        }
        Template::Set(c) => Kind::set(instance(c, names, store)),
        Template::Property(c) => Kind::Property(Box::new(instance(c, names, store))),
        Template::Function(a, b) => {
            let a = instance(a, names, store);
            let b = instance(b, names, store);
            Kind::Function(Box::new(a), Box::new(b))
        }
    }
}

regex!(
    TOKEN,
    r"group-element|set of|property of|function from|to|number|point|formula|[α-ω]"
);

/// A `kinds` field, or a decline saying what in it does not read.
/// `check_notation` reports that; everything else skips a notation whose
/// field is one.
pub fn signature(text: &str) -> Route<Signature> {
    let Some((holes_text, result_text)) = text.split_once('→') else {
        return Route::no(format!("{} has no `→` before what it produces", repr(text)));
    };
    let holes: Vec<&str> = holes_text
        .split(',')
        .map(pystr::strip)
        .filter(|h| !h.is_empty())
        .collect();
    let mut templates = Vec::new();
    for h in holes.iter().copied().chain([pystr::strip(result_text)]) {
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

fn read_template(text: &str) -> Route<Template> {
    let tokens: Vec<&str> = TOKEN.find_iter(text).map(|m| m.as_str()).collect();
    if tokens.concat().replace(' ', "") != text.replace(' ', "") {
        return Route::no(format!("{} is not a kind", repr(text)));
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
        return Route::no("a kind is missing");
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

/// Kinds over one statement or proof, read in the order it is written.
///
/// `env` maps a name to its kind; a `let` shadows what came before, since a
/// block may use a letter an earlier one did. What does not fit is kept in
/// `clashes`.
pub struct Reader {
    pub env: IndexMap<String, Kind>,
    pub clashes: Vec<Clash>,
    /// Names declared of any kind, not yet fixed.
    declared: Vec<String>,
    signatures: IndexMap<String, Rc<Signature>>,
    bound: IndexMap<String, IndexSet<usize>>,
}

impl Reader {
    pub fn new(env: Env) -> Reader {
        let mut signatures: IndexMap<String, Rc<Signature>> = IndexMap::new();
        let mut bound: IndexMap<String, IndexSet<usize>> = IndexMap::new();
        for n in &env.g.notations {
            let key = n.key().to_string();
            let Some(kinds) = &n.kinds else { continue };
            if kinds.is_empty() {
                continue;
            }
            let Built(made) = signature(kinds) else {
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
        Reader {
            env: IndexMap::new(),
            clashes: Vec::new(),
            declared: Vec::new(),
            signatures,
            bound,
        }
    }

    fn of_name(&mut self, name: &str, store: &mut Store) -> Kind {
        if let Some(k) = self.env.get(name) {
            return k.clone();
        }
        let k = store.var();
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

    /// The kind of a parse tree, noting every clash inside it.
    pub fn kind(
        &mut self,
        node: &Node,
        line: At,
        local: &IndexMap<String, Kind>,
        store: &mut Store,
    ) -> Kind {
        if node.is_name() {
            if let Some(k) = local.get(&node.text) {
                return k.clone();
            }
            return self.of_name(&node.text, store);
        }
        if node.notation == "numeral" {
            return NUMBER;
        }
        let (holes, out) = match self.signatures.get(&node.notation).cloned() {
            Some(make) if make.holes() == node.children.len() => make.fresh(store),
            _ => by_sort(node, store),
        };
        let mut inner = local.clone();
        if let Some(indices) = self.bound.get(&node.notation).cloned() {
            for i in indices {
                if i < node.children.len() && node.children[i].is_name() {
                    let v = store.var();
                    inner.insert(node.children[i].text.clone(), v);
                }
            }
        }
        for (child, want) in node.children.iter().zip(holes.iter()) {
            let got = self.kind(child, line, &inner, store);
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
        let k = self.kind(node, line, &IndexMap::new(), store);
        if let Declined(said) = store.unify(&k, &FORMULA) {
            self.clash(line, "the line", &said);
        }
    }

    /// Make what the declared names' kinds still leave open rigid.
    ///
    /// Called once the lines declaring them are read: the statement's
    /// hypotheses and conclusion, or a block's opening lines. What they
    /// related is related; what they left open is "any kind" from here on,
    /// and a proof that narrows it is proving less than it claims.
    pub fn fix_declared(&mut self, store: &mut Store) {
        for name in std::mem::take(&mut self.declared) {
            if let Some(k) = self.env.get(&name).cloned() {
                store.make_rigid(&k, &name);
            }
        }
    }
}

fn by_sort(node: &Node, store: &mut Store) -> (Vec<Kind>, Kind) {
    fn of(sort: &Sort, store: &mut Store) -> Kind {
        match sort.name() {
            Some("number") => NUMBER,
            Some("point") => POINT,
            Some("formula") => FORMULA,
            Some("set") => Kind::set(store.var()),
            Some("group-element") => GROUP_ELEMENT,
            Some("group-set") => Kind::set(GROUP_ELEMENT),
            Some("set-of-sets") => Kind::set(Kind::set(store.var())),
            _ => store.var(),
        }
    }
    let holes = node.children.iter().map(|c| of(&c.sort, store)).collect();
    let out = of(&node.sort, store);
    (holes, out)
}

regex!(INTRODUCED_NAME, r"^([^\s∈∉:]+)\s*(?:∈|∉|:)");

/// What a `let` line says a name is, into the reader's kinds.
///
/// `be a set` and `be an element` declare a thing of any kind. The lines
/// declaring it may still relate it to another — `X ∖ {a}` makes a the kind
/// of what X holds — so the kind is left free here and noted in `declared`,
/// and `fix_declared` fixes it once the statement or the block's opening
/// lines are read. The rest name a thing whose kind the text fixes, and the
/// line is read as a claim.
pub fn introduce(
    reader: &mut Reader,
    body: &str,
    line: At,
    env: Env,
    sorts: &Sorts,
    store: &mut Store,
) {
    let body = pystr::strip(&unlabel(body)).to_string();
    // A group is a set of group elements, and its identity is one of them.
    if let Some(m) = group_re().captures(&body) {
        reader
            .env
            .insert(m["group"].to_string(), Kind::set(GROUP_ELEMENT));
        reader.env.insert(m["identity"].to_string(), GROUP_ELEMENT);
        return;
    }
    if let Some(m) = kind_re().captures(&body) {
        let name = m[1].to_string();
        if &m[2] == "set" {
            let v = store.var_said(false, &name);
            reader.env.insert(name.clone(), Kind::set(v));
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
            .insert(m[1].to_string(), Kind::Property(Box::new(of.clone())));
        let domain = reader.of_name(&m[2], store);
        if let Declined(said) = store.unify(&domain, &Kind::set(of)) {
            reader.clash(line, &m[2], &said);
        }
        return;
    }
    let body = let_formula(&body);
    if let Some(m) = INTRODUCED_NAME.captures(&body) {
        let v = store.var();
        reader.env.insert(m[1].to_string(), v);
    }
    claim_text(reader, &body, line, env, sorts, store);
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
    sorts: &Sorts,
    store: &mut Store,
) {
    for sentence in sentences(text) {
        let Ok(node) = parse_here(&sentence, env.g, sorts) else {
            continue;
        };
        reader.claim(&node, line, store);
    }
}

/// An item's kinds, read from its own lines in the order they are written.
///
/// A record keeps the keyword of a hypothesis in the field name where a
/// proof line keeps it in the text, and has no steps.
pub fn read_record(
    record: &Record,
    env: Env,
    sorts: &Sorts,
    store: &mut Store,
) -> Reader {
    let mut reader = Reader::new(env);
    for h in &record.hypotheses {
        if h.kind == Intro::Let {
            introduce(&mut reader, &h.text, h.line.into(), env, sorts, store);
        } else {
            let text = pystr::strip(&unlabel(&h.text)).to_string();
            claim_text(&mut reader, &text, h.line.into(), env, sorts, store);
        }
    }
    for (text, no) in &record.conclusions {
        claim_text(&mut reader, text, (*no).into(), env, sorts, store);
    }
    reader
}

/// The kinds of the sequences a define by recursion gives: each takes a
/// number, the index, and gives what its value at 0 is, which each rule at
/// k + 1 must give too. Every name is in scope in every rule, since a rule
/// may name any of the sequences at k.
fn recursion_kinds(
    reader: &mut Reader,
    said: &crate::corpus::Recursion,
    line: At,
    env: Env,
    sorts: &Sorts,
    store: &mut Store,
) {
    let mut gives: IndexMap<String, Kind> = IndexMap::new();
    for name in &said.names {
        gives.insert(name.clone(), store.var());
    }
    for name in &said.names {
        reader.env.insert(
            name.clone(),
            Kind::Function(Box::new(NUMBER), Box::new(gives[name].clone())),
        );
    }
    let mut local_sorts = sorts.clone();
    local_sorts.insert(said.index.clone(), Sort::of("number"));
    let mut at_step = IndexMap::new();
    at_step.insert(said.index.clone(), NUMBER);
    for (rules, local) in [(&said.start, IndexMap::new()), (&said.step, at_step)] {
        for (name, rule) in rules {
            let Ok(tree) = parse_here(rule, env.g, &local_sorts) else {
                continue; // `check_formulas` says it does not read
            };
            let got = reader.kind(&tree, line, &local, store);
            if let Declined(fits) = store.unify(&got, &gives[name]) {
                reader.clash(line, name, &fits);
            }
        }
    }
}

/// What a step's citations are fitted against, called after its claim is
/// read.
pub type Cite<'c> = &'c mut dyn FnMut(&mut Reader, &mut Store, &Step);

/// A theorem's kinds, read in the order its lines are written.
///
/// A `let` shadows an earlier name, since blocks reuse letters. What the
/// statement or a block's opening lines declared of any kind is fixed where
/// the proof under them begins. `cite` is called after each step's claim is
/// read, for whoever fits its citations.
pub fn read_theorem(
    thm: &Theorem,
    env: Env,
    sorts: &Sorts,
    store: &mut Store,
    mut cite: Option<Cite>,
) -> Reader {
    let mut reader = Reader::new(env);
    // What the theorem sees from outside it has its kind before its first
    // line, read from the rule written out where it was defined.
    for (name, made) in file_definitions(thm, env) {
        let kind = match made {
            Defined::Rule(rule) => {
                let taken = store.var();
                let mut local = IndexMap::new();
                local.insert(rule.param.clone(), taken.clone());
                let gives = reader.kind(&rule.body, thm.line.into(), &local, store);
                Kind::Function(Box::new(taken), Box::new(gives))
            }
            Defined::Term(t) => {
                reader.kind(&t, thm.line.into(), &IndexMap::new(), store)
            }
        };
        reader.env.insert(name, kind);
    }
    enum Event<'t> {
        Let(&'t str),
        Said(String),
        Define(&'t str),
        Claim(&'t Step),
    }
    // Each line, where it stands, and whether reading it first fixes what
    // was declared of any kind: a define, a claim and a requires line do,
    // since the proof has begun by then.
    let mut events: Vec<(At, bool, Event)> = Vec::new();
    fn opening(kind: Intro, text: &str) -> Event<'_> {
        let rest = &text[kind.as_str().len()..];
        if kind == Intro::Let {
            Event::Let(rest)
        } else {
            Event::Said(pystr::strip(&unlabel(rest)).to_string())
        }
    }
    for h in &thm.hypotheses {
        events.push((h.line.into(), false, opening(h.kind, &h.text)));
    }
    // The conclusion is the statement's last line, so it may still relate
    // what the hypotheses declared of any kind.
    let after = thm
        .hypotheses
        .iter()
        .map(|h| h.line)
        .max()
        .unwrap_or(thm.line);
    events.push((
        At::after(after),
        false,
        Event::Said(pystr::strip(&unlabel(&thm.conclusion)).to_string()),
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
                Event::Said(pystr::strip(&unlabel(&r.fact)).to_string()),
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
            Event::Let(text) => introduce(&mut reader, text, no, env, sorts, store),
            Event::Said(text) => claim_text(&mut reader, text, no, env, sorts, store),
            Event::Define(text) => {
                let Built(said) = define_parts(text) else {
                    continue;
                };
                let said = match said {
                    DefineParts::Recursion(r) => {
                        recursion_kinds(&mut reader, &r, no, env, sorts, store);
                        continue;
                    }
                    DefineParts::One(d) => d,
                };
                let Some(param) = &said.param else {
                    let Ok(tree) = parse_here(&said.body, env.g, sorts) else {
                        continue;
                    };
                    let k = reader.kind(&tree, no, &IndexMap::new(), store);
                    reader.env.insert(said.name.clone(), k);
                    continue;
                };
                // A function: what its domain holds goes in, what its rule
                // gives comes out, and the parameter is its rule's own name.
                let local_sorts = define_sorts(&said, sorts);
                let domain = said.domain.clone().unwrap_or_default();
                let Ok(over_tree) = parse_here(&domain, env.g, &local_sorts) else {
                    continue;
                };
                let over = reader.kind(&over_tree, no, &IndexMap::new(), store);
                let taken = store.var();
                if let Declined(said_of) = store.unify(&over, &Kind::set(taken.clone()))
                {
                    reader.clash(no, domain.clone(), &said_of);
                }
                let Ok(body_tree) = parse_here(&said.body, env.g, &local_sorts) else {
                    continue;
                };
                let mut local = IndexMap::new();
                local.insert(param.clone(), taken.clone());
                let gives = reader.kind(&body_tree, no, &local, store);
                reader.env.insert(
                    said.name.clone(),
                    Kind::Function(Box::new(taken), Box::new(gives)),
                );
            }
            Event::Claim(step) => {
                let obtained = if step.just.head.is(Method::Obtain) {
                    obtains(&step.just.text)
                } else {
                    None
                };
                if let Some(names) = obtained {
                    for name in split_names(pystr::strip(&names)) {
                        let v = store.var();
                        reader.env.insert(name.to_string(), v);
                    }
                }
                claim_text(&mut reader, &step.claim_text(), no, env, sorts, store);
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

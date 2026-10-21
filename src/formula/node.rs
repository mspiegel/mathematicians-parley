//! A parsed formula.

use std::cell::{Cell, OnceCell};
use std::collections::BTreeSet;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::sync::Arc;

use super::notation_id::{LiteralId, NotationId, Spelling, NO_LITERAL};
use super::symbol::Symbol;
use crate::mm::Rpn;
use crate::notations::{LITERAL, NAME, NUMERAL, PROPERTY_OF};

/// The sort of a node: what kind of thing its term is, or none at all.
///
/// Sorts nest: a number, a set of numbers and a set of sets of numbers are
/// three sorts, and a set of things of a sort not settled is a fourth. Where
/// the reading of the lines settled a name's sort it is here whole. The
/// parser tells readings apart by a coarser class, the sort's category (a
/// number, a set, a set of sets, a function, …), which is all a notation's
/// hole asks for and all a parse tree's node knows of what it yields.
///
/// "None" is kept apart from "unknown": they are printed differently where a
/// message names a sort.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Sort {
    category: Option<Category>,
    whole: Option<Rc<Whole>>,
}

/// A sort's category by name. The categories the code itself names are
/// variants, so that a sort of one is made without allocating; any other
/// name a record or a sort line writes, a sort variable `α` among them, is
/// kept as written. `Category::of` makes a known name its variant always,
/// so two categories are equal exactly where their names are.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Category {
    Number,
    Point,
    Formula,
    GroupElement,
    Set,
    GroupSet,
    SetOfSets,
    Property,
    Function,
    Any,
    Variable,
    Unknown,
    Named(Rc<str>),
}

impl Category {
    fn of(name: &str) -> Category {
        match name {
            "number" => Category::Number,
            "point" => Category::Point,
            "formula" => Category::Formula,
            "group-element" => Category::GroupElement,
            "set" => Category::Set,
            "group-set" => Category::GroupSet,
            "set-of-sets" => Category::SetOfSets,
            "property" => Category::Property,
            "function" => Category::Function,
            "any" => Category::Any,
            "variable" => Category::Variable,
            "unknown" => Category::Unknown,
            other => Category::Named(Rc::from(other)),
        }
    }

    fn name(&self) -> &str {
        match self {
            Category::Number => "number",
            Category::Point => "point",
            Category::Formula => "formula",
            Category::GroupElement => "group-element",
            Category::Set => "set",
            Category::GroupSet => "group-set",
            Category::SetOfSets => "set-of-sets",
            Category::Property => "property",
            Category::Function => "function",
            Category::Any => "any",
            Category::Variable => "variable",
            Category::Unknown => "unknown",
            Category::Named(name) => name,
        }
    }
}

/// A sort in full, as the reading of the lines settles it.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Whole {
    Number,
    Point,
    Formula,
    GroupElement,
    Set(Rc<Whole>),
    Property(Rc<Whole>),
    Function(Rc<Whole>, Rc<Whole>),
    /// A pair, of the sorts of its first and second parts.
    Pair(Rc<Whole>, Rc<Whole>),
    /// A sort the lines leave open.
    Open,
}

impl Whole {
    /// A sort as a record's `sort` line writes it in full, `set of function
    /// from number to number`; None for one that names a sort variable or a
    /// word it does not know.
    pub fn read(text: &str) -> Option<Whole> {
        let text = str::trim(text);
        if let Some(rest) = text.strip_prefix("set of ") {
            return Some(Whole::Set(Rc::new(Whole::read(rest)?)));
        }
        if let Some(rest) = text.strip_prefix("property of ") {
            return Some(Whole::Property(Rc::new(Whole::read(rest)?)));
        }
        if let Some(rest) = text.strip_prefix("function from ") {
            let (from, to) = rest.split_once(" to ")?;
            return Some(Whole::Function(
                Rc::new(Whole::read(from)?),
                Rc::new(Whole::read(to)?),
            ));
        }
        if let Some(rest) = text.strip_prefix("pair of ") {
            let (first, second) = rest.split_once(" and ")?;
            return Some(Whole::Pair(
                Rc::new(Whole::read(first)?),
                Rc::new(Whole::read(second)?),
            ));
        }
        Some(match text {
            "number" => Whole::Number,
            "point" => Whole::Point,
            "formula" => Whole::Formula,
            "group-element" => Whole::GroupElement,
            _ => return None,
        })
    }

    /// The sort as a reader would say it: `a set of numbers`.
    pub fn describe(&self) -> String {
        match self {
            Whole::Number => "a number".into(),
            Whole::Point => "a point".into(),
            Whole::Formula => "a statement".into(),
            Whole::GroupElement => "a group element".into(),
            Whole::Set(k) => format!("a set of {}", plural(&k.describe())),
            Whole::Property(k) => format!("a property of {}", plural(&k.describe())),
            Whole::Function(a, b) => format!(
                "a function from {} to {}",
                plural(&a.describe()),
                plural(&b.describe())
            ),
            Whole::Pair(a, b) => {
                format!("a pair of {} and {}", a.describe(), b.describe())
            }
            Whole::Open => "a thing of a sort not yet settled".into(),
        }
    }

    /// The coarse class the parser tells readings apart by, or None for a
    /// sort that has none: a statement, or one left open.
    pub fn category(&self) -> Option<&'static str> {
        Some(match self {
            Whole::Number => "number",
            Whole::Point => "point",
            Whole::GroupElement => "group-element",
            Whole::Set(inner) => match &**inner {
                Whole::GroupElement => "group-set",
                Whole::Set(_) => "set-of-sets",
                _ => "set",
            },
            Whole::Property(_) => "property",
            Whole::Function(..) => "function",
            Whole::Pair(..) => "pair",
            Whole::Formula | Whole::Open => return None,
        })
    }
}

/// `a number` as `numbers`, `a set of X` as `sets of X`: the phrase for many
/// of what `one` names one of.
pub fn plural(one: &str) -> String {
    for (a, many) in [
        ("a number", "numbers"),
        ("a point", "points"),
        ("a group element", "group elements"),
        ("a statement", "statements"),
        ("a set of", "sets of"),
        ("a property of", "properties of"),
        ("a function from", "functions from"),
        ("a pair of", "pairs of"),
        ("a thing of", "things of"),
        ("a name", "names"),
        ("a term", "terms"),
    ] {
        if let Some(rest) = one.strip_prefix(a) {
            return format!("{many}{rest}");
        }
    }
    format!("things that are {one}")
}

/// A category as a reader would say it: what a hole wants.
pub fn describe_category(category: &str) -> String {
    match category {
        "number" => "a number",
        "point" => "a point",
        "formula" => "a statement",
        "group-element" => "a group element",
        "set" => "a set",
        "group-set" => "a set of group elements",
        "set-of-sets" => "a set of sets",
        "function" => "a function",
        "pair" => "a pair",
        "property" => "a property",
        "variable" => "a name",
        _ => "a term",
    }
    .to_string()
}

impl Sort {
    /// The sort as a reader would say it, in full where the reading of the
    /// lines settled it and by its category otherwise.
    pub fn describe(&self) -> String {
        match (&self.whole, self.name()) {
            (Some(whole), _) => whole.describe(),
            (None, None) | (None, Some("unknown")) => "of no sort yet".into(),
            (None, Some(category)) => describe_category(category),
        }
    }

    pub fn none() -> Sort {
        Sort::default()
    }

    /// A sort known only by its category, as a notation says what it yields.
    pub fn of(name: &str) -> Sort {
        Sort {
            category: Some(Category::of(name)),
            whole: None,
        }
    }

    /// A sort in full, or None where it has no category.
    pub fn whole(whole: Whole) -> Option<Sort> {
        let category = whole.category()?;
        Some(Sort {
            category: Some(Category::of(category)),
            whole: Some(Rc::new(whole)),
        })
    }

    pub fn unknown() -> Sort {
        Sort::of("unknown")
    }

    /// The sort in full, where the reading settled it.
    pub fn full(&self) -> Option<&Whole> {
        self.whole.as_deref()
    }

    /// The sort's category, or None for no sort.
    pub fn name(&self) -> Option<&str> {
        self.category.as_ref().map(Category::name)
    }

    /// The sort of what a set of this sort holds, where it says: a set of
    /// numbers holds numbers, a group's set its elements, and a set of sets
    /// sets.
    pub fn held(&self) -> Option<Sort> {
        if let Some(whole) = &self.whole {
            return match &**whole {
                Whole::Set(inner) => inner.category().map(|category| Sort {
                    category: Some(Category::of(category)),
                    whole: Some(inner.clone()),
                }),
                _ => None,
            };
        }
        match self.name() {
            Some("group-set") => Some(Sort::of("group-element")),
            Some("set-of-sets") => Some(Sort::of("set")),
            _ => None,
        }
    }

    pub fn is(&self, name: &str) -> bool {
        self.name() == Some(name)
    }

    /// Whether this is no sort, `unknown`, or `any`: the three a value of no
    /// known sort is written as.
    pub fn is_unsorted(&self) -> bool {
        matches!(self.name(), None | Some("unknown") | Some("any"))
    }

    /// Whether this is no sort or `unknown`.
    pub fn is_unknown(&self) -> bool {
        matches!(self.name(), None | Some("unknown"))
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name().unwrap_or("None"))
    }
}

pub struct NodeData {
    pub sort: Sort,
    pub children: Vec<Node>,
    /// A letter's name, a numeral's digits, or a notation node's literal.
    pub text: Symbol,
    /// The notation and the literal as ids (`Node::notation`,
    /// `Node::spelling`).
    notation_id: NotationId,
    literal_id: LiteralId,
    /// For a node standing in for a term the elaborator already holds, the
    /// term in reverse Polish.
    pub rpn: Option<Rpn>,
    shape: OnceCell<String>,
    /// A hash of the shape, worked out from the parts and not the text
    /// (`same_shape`).
    shape_hash: OnceCell<u64>,
    /// The characters of the sentence the parser read this node from, for
    /// a tool that restates a part of what was written; none for a node
    /// built any other way.
    span: Cell<Option<(usize, usize)>>,
    /// Whether the text wrote this node inside brackets, which closes it:
    /// what follows extends the group whatever its level.
    grouped: Cell<bool>,
}

/// A parsed formula: a notation, the sort of what it builds, its children,
/// and the literal that stands in it.
///
/// Nodes are shared, and a node's identity is meaningful: which occurrence
/// of a property may decide what it stands for is a set of occurrences, not
/// of shapes (`matching::binding_sites`).
#[derive(Clone)]
pub struct Node(Rc<NodeData>);

impl std::ops::Deref for Node {
    type Target = NodeData;
    fn deref(&self) -> &NodeData {
        &self.0
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.shape())
    }
}

/// A node's identity, for sets of occurrences.
pub type NodeId = usize;

/// A node as a key by its shape: two keys are equal where their nodes have
/// one shape (`Node::same_shape`), for a set of formulas told apart as
/// `shape` tells them.
#[derive(Clone, Debug)]
pub struct ByShape(pub Node);

impl PartialEq for ByShape {
    fn eq(&self, other: &ByShape) -> bool {
        self.0.same_shape(&other.0)
    }
}

impl Eq for ByShape {}

impl Hash for ByShape {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.shape_hash());
    }
}

impl Node {
    fn made(spelling: Spelling, sort: Sort, children: Vec<Node>, text: Symbol) -> Node {
        Node(Rc::new(NodeData {
            sort,
            children,
            text,
            notation_id: spelling.notation,
            literal_id: spelling.literal,
            rpn: None,
            shape: OnceCell::new(),
            shape_hash: OnceCell::new(),
            span: Cell::new(None),
            grouped: Cell::new(false),
        }))
    }

    /// A node of a notation, written with one of its literals.
    pub fn of(spelling: Spelling, sort: Sort, children: Vec<Node>) -> Node {
        Node::made(spelling, sort, children, spelling.text())
    }

    /// A letter.
    pub fn name(sort: Sort, letter: &str) -> Node {
        Node::made(
            Spelling::new(NAME, NO_LITERAL),
            sort,
            Vec::new(),
            Symbol::of(letter),
        )
    }

    /// A numeral, its digits as written.
    pub fn numeral(digits: &str) -> Node {
        Node::made(
            Spelling::new(NUMERAL, NO_LITERAL),
            Sort::of("number"),
            Vec::new(),
            Symbol::of(digits),
        )
    }

    /// What a property stands for: `body` with the letter `hole` marked as
    /// its hole. No text is parsed as one; it exists only inside a binding.
    pub fn property(hole: &str, body: Node) -> Node {
        Node::made(
            Spelling::new(PROPERTY_OF, NO_LITERAL),
            Sort::of("property"),
            vec![body],
            Symbol::of(hole),
        )
    }

    /// This node with other children: its notation, literal, text and sort
    /// kept, and nothing of where it was read or what term it stood for.
    pub fn with_children(&self, children: Vec<Node>) -> Node {
        Node(Rc::new(NodeData {
            sort: self.sort.clone(),
            children,
            text: self.text,
            notation_id: self.notation_id,
            literal_id: self.literal_id,
            rpn: None,
            shape: OnceCell::new(),
            shape_hash: OnceCell::new(),
            span: Cell::new(None),
            grouped: Cell::new(false),
        }))
    }

    /// The node's notation.
    pub fn notation(&self) -> NotationId {
        self.notation_id
    }

    /// The name of the node's notation, as its record declares it: for a
    /// message, and for the node's shape.
    pub fn notation_name(&self) -> Arc<str> {
        self.notation_id.name()
    }

    /// The node's notation and the literal it is written with.
    pub fn spelling(&self) -> Spelling {
        Spelling::new(self.notation_id, self.literal_id)
    }

    /// Whether the text wrote this node inside brackets.
    pub fn grouped(&self) -> bool {
        self.grouped.get()
    }

    /// Say that the text wrote this node inside brackets.
    pub fn set_grouped(&self) {
        self.grouped.set(true);
    }

    /// Where in the sentence the parser read this node from, as character
    /// offsets, end exclusive.
    pub fn span(&self) -> Option<(usize, usize)> {
        self.span.get()
    }

    /// Say where the parser read this node from. A span runs forwards, which
    /// `written` relies on, so one that does not is the parser's fault and
    /// stops it where it is made.
    pub fn set_span(&self, from: usize, to: usize) {
        assert!(
            from <= to,
            "a span runs forwards, and {} was given {from}..{to}",
            self.notation_name()
        );
        self.span.set(Some((from, to)));
    }

    /// The text the parser read this node from, cut from the sentence it
    /// read; None for a node it did not read.
    pub fn written(&self, sentence: &str) -> Option<String> {
        let (from, to) = self.span()?;
        Some(sentence.chars().skip(from).take(to - from).collect())
    }

    /// The same tree read from no sentence: for a node standing where the
    /// text wrote nothing, as the declared set does in "for all ε > 0", so
    /// that nothing cuts text for it from a sentence it was not read from.
    pub fn unwritten(&self) -> Node {
        Node(Rc::new(NodeData {
            sort: self.sort.clone(),
            children: self.children.iter().map(Node::unwritten).collect(),
            text: self.text,
            notation_id: self.notation_id,
            literal_id: self.literal_id,
            rpn: self.rpn.clone(),
            shape: OnceCell::new(),
            shape_hash: OnceCell::new(),
            span: Cell::new(None),
            grouped: Cell::new(self.grouped()),
        }))
    }

    /// A term already in kernel form, standing in a tree: notation
    /// `literal`, no sort, no children and no text.
    pub fn literal(rpn: &Rpn) -> Node {
        Node(Rc::new(NodeData {
            sort: Sort::none(),
            children: Vec::new(),
            text: Symbol::default(),
            notation_id: LITERAL,
            literal_id: NO_LITERAL,
            rpn: Some(rpn.clone()),
            shape: OnceCell::new(),
            shape_hash: OnceCell::new(),
            span: Cell::new(None),
            grouped: Cell::new(false),
        }))
    }

    pub fn id(&self) -> NodeId {
        Rc::as_ptr(&self.0) as usize
    }

    pub fn same(&self, other: &Node) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }

    pub fn is_name(&self) -> bool {
        self.notation_id == NAME
    }

    /// The leftmost leaf of the tree: the name a `let` line introduces, and
    /// the letter a definition is about.
    pub fn leftmost(&self) -> &Node {
        let mut node = self;
        while let Some(first) = node.children.first() {
            node = first;
        }
        node
    }

    /// A parenthesis-free rendering, which is what two instances are
    /// compared by. Layout plays no part once the tree is built.
    ///
    /// The literal is part of it wherever there is one, because a record may
    /// declare several patterns and they are different formulas: `a < b` and
    /// `a ≥ b` are both `order`, and only the sign tells them apart.
    pub fn shape(&self) -> &str {
        self.shape.get_or_init(|| {
            let notation = self.notation_name();
            let head = if self.text.is_empty() {
                notation.to_string()
            } else {
                format!("{notation}:{}", self.text)
            };
            if self.children.is_empty() {
                return head;
            }
            let inner: Vec<&str> = self.children.iter().map(|c| c.shape()).collect();
            format!("{head}({})", inner.join(", "))
        })
    }

    /// Whether the two have one shape: the same notation, text and
    /// children's shapes, as `shape` writes them, compared part by part and
    /// with no text built. The hashes settle most pairs that differ.
    pub fn same_shape(&self, other: &Node) -> bool {
        self.same(other)
            || (self.shape_hash() == other.shape_hash()
                && self.notation_id == other.notation_id
                && self.text == other.text
                && self.children.len() == other.children.len()
                && self
                    .children
                    .iter()
                    .zip(&other.children)
                    .all(|(a, b)| a.same_shape(b)))
    }

    /// A hash of the shape, the same for two nodes `same_shape` holds of,
    /// worked out once.
    pub fn shape_hash(&self) -> u64 {
        *self.shape_hash.get_or_init(|| {
            let mut state = rustc_hash::FxHasher::default();
            self.notation_id.hash(&mut state);
            self.text.hash(&mut state);
            self.children.len().hash(&mut state);
            for c in &self.children {
                c.shape_hash().hash(&mut state);
            }
            state.finish()
        })
    }

    /// The node as a key that two nodes of one shape share (`same_shape`).
    pub fn by_shape(&self) -> ByShape {
        ByShape(self.clone())
    }

    /// The names the formula uses.
    pub fn names(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.gather_names(&mut out);
        out
    }

    fn gather_names(&self, out: &mut BTreeSet<String>) {
        if self.children.is_empty() {
            if self.is_name() {
                out.insert(self.text.to_string());
            }
            return;
        }
        for c in &self.children {
            c.gather_names(out);
        }
    }

    /// The node and every node under it, in the order a walk meets them.
    pub fn walk(&self) -> Vec<Node> {
        let mut out = Vec::new();
        let mut stack = vec![self.clone()];
        while let Some(n) = stack.pop() {
            for c in n.children.iter().rev() {
                stack.push(c.clone());
            }
            out.push(n);
        }
        out
    }
}

/// Every node of every tree, in order.
pub fn walk(nodes: &[Node]) -> Vec<Node> {
    nodes.iter().flat_map(|n| n.walk()).collect()
}

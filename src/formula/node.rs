//! A parsed formula.

use std::cell::{Cell, OnceCell};
use std::collections::BTreeSet;
use std::fmt;
use std::rc::Rc;

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
    category: Option<Rc<str>>,
    whole: Option<Rc<Whole>>,
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
    /// A sort the lines leave open.
    Open,
}

impl Whole {
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
            category: Some(Rc::from(name)),
            whole: None,
        }
    }

    /// A sort in full, or None where it has no category.
    pub fn whole(whole: Whole) -> Option<Sort> {
        let category = whole.category()?;
        Some(Sort {
            category: Some(Rc::from(category)),
            whole: Some(Rc::new(whole)),
        })
    }

    pub fn unknown() -> Sort {
        Sort::of("unknown")
    }

    /// The sort's category, or None for no sort.
    pub fn name(&self) -> Option<&str> {
        self.category.as_deref()
    }

    /// The sort of what a set of this sort holds, where it says: a set of
    /// numbers holds numbers, a group's set its elements, and a set of sets
    /// sets.
    pub fn held(&self) -> Option<Sort> {
        if let Some(whole) = &self.whole {
            return match &**whole {
                Whole::Set(inner) => Sort::whole((**inner).clone()),
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
    pub notation: String,
    pub sort: Sort,
    pub children: Vec<Node>,
    pub text: String,
    /// For a node standing in for a term the elaborator already holds, the
    /// term in reverse Polish.
    pub literal: Option<Rc<str>>,
    shape: OnceCell<String>,
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

impl Node {
    pub fn new(notation: &str, sort: Sort, children: Vec<Node>, text: &str) -> Node {
        Node(Rc::new(NodeData {
            notation: notation.to_string(),
            sort,
            children,
            text: text.to_string(),
            literal: None,
            shape: OnceCell::new(),
            span: Cell::new(None),
            grouped: Cell::new(false),
        }))
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

    /// Say where the parser read this node from.
    pub fn set_span(&self, from: usize, to: usize) {
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
            notation: self.notation.clone(),
            sort: self.sort.clone(),
            children: self.children.iter().map(Node::unwritten).collect(),
            text: self.text.clone(),
            literal: self.literal.clone(),
            shape: OnceCell::new(),
            span: Cell::new(None),
            grouped: Cell::new(self.grouped()),
        }))
    }

    /// A term already in kernel form, standing in a tree: notation
    /// `literal`, no sort, no children and no text.
    pub fn literal(rpn: &str) -> Node {
        Node(Rc::new(NodeData {
            notation: "literal".to_string(),
            sort: Sort::none(),
            children: Vec::new(),
            text: String::new(),
            literal: Some(Rc::from(rpn)),
            shape: OnceCell::new(),
            span: Cell::new(None),
            grouped: Cell::new(false),
        }))
    }

    pub fn leaf(notation: &str, sort: Sort, text: &str) -> Node {
        Node::new(notation, sort, Vec::new(), text)
    }

    pub fn id(&self) -> NodeId {
        Rc::as_ptr(&self.0) as usize
    }

    pub fn same(&self, other: &Node) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }

    pub fn is_name(&self) -> bool {
        self.notation == "name"
    }

    /// A parenthesis-free rendering, which is what two instances are
    /// compared by. Layout plays no part once the tree is built.
    ///
    /// The literal is part of it wherever there is one, because a record may
    /// declare several patterns and they are different formulas: `a < b` and
    /// `a ≥ b` are both `order`, and only the sign tells them apart.
    pub fn shape(&self) -> &str {
        self.shape.get_or_init(|| {
            let head = if self.text.is_empty() {
                self.notation.clone()
            } else {
                format!("{}:{}", self.notation, self.text)
            };
            if self.children.is_empty() {
                return head;
            }
            let inner: Vec<&str> = self.children.iter().map(|c| c.shape()).collect();
            format!("{head}({})", inner.join(", "))
        })
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
                out.insert(self.text.clone());
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

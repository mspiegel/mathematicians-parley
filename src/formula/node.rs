//! A parsed formula.

use std::cell::OnceCell;
use std::collections::BTreeSet;
use std::fmt;
use std::rc::Rc;

/// The sort of a node: what kind of thing its term is, as the notation
/// database names sorts, or none at all.
///
/// Sorts are the database's words, so they are text and not a closed list.
/// "None" is kept apart from "unknown": they are printed differently where a
/// message names a sort.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Sort(Option<Rc<str>>);

impl Sort {
    pub fn none() -> Sort {
        Sort(None)
    }

    pub fn of(name: &str) -> Sort {
        Sort(Some(Rc::from(name)))
    }

    pub fn unknown() -> Sort {
        Sort::of("unknown")
    }

    /// The sort's name, or None for no sort.
    pub fn name(&self) -> Option<&str> {
        self.0.as_deref()
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

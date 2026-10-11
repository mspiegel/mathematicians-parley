//! A `let` line's introduction, read once (`GRAMMAR.md`, an introduction
//! is not a formula).
//!
//! A `let` line names something and says what it is, in one of the forms
//! `GRAMMAR.md` lists. Which form is the skeleton's to read, by pattern, and
//! the parts of a form that are formulas, a set or a function's type, are
//! formula text, read by the front end. What the line asserts is made from
//! those parts as trees (`asserted`), never written out as text and parsed.

use crate::formula::page::{filled, made_as, Written};
use crate::formula::{Grammar, Node, Sorts};
use crate::outcome::Checked;

use super::{
    element_re, function_being_re, function_on_re, function_re, graph_line, group_re,
    membership_re, not_in_re, part_re, polynomial_re, property_re, set_or_point_re,
    GraphLine,
};

/// A `let` line's introduction: what it says after `let`, its label taken
/// off, and which form it takes.
#[derive(Clone)]
pub struct Introduction {
    pub body: Written,
    pub form: Form,
}

/// The forms an introduction takes, each with the parts it names.
#[derive(Clone)]
pub enum Form {
    /// `G be the undirected multigraph with distinct vertices V = {…} and
    /// distinct edges E = {…}, where a joins A and B, …`.
    GraphListed(GraphLine),
    /// `G be an undirected multigraph with vertices V and edges E`.
    Graph(GraphLine),
    /// `G be a finite group with operation · and identity e`.
    Group {
        group: String,
        finite: bool,
        identity: String,
    },
    /// `A be a set`.
    Set(String),
    /// `P be a point`.
    Point(String),
    /// `x be an element`.
    Element(String),
    /// `P be a property of the elements of A`.
    Property { name: String, domain: String },
    /// `E be a function on X`.
    FunctionOn { name: String, set: String },
    /// `p be a polynomial`.
    Polynomial(String),
    /// `f : A → B be one-to-one`: the type, and what follows `be`.
    FunctionBeing { typed: String, being: String },
    /// `f : A → B`.
    Function,
    /// `X ⊆ A`.
    Part { name: String, whole: String },
    /// `a ∉ X`.
    NotIn(String),
    /// `x ∈ A`.
    Member,
    /// None of the forms, which `check_introductions` reports.
    Other,
}

impl Introduction {
    /// The introduction `body` says, the text after `let` with its label
    /// taken off.
    pub fn read(body: Written) -> Introduction {
        let text = body.text();
        let name = |m: &regex::Captures| m[1].to_string();
        let form = if let Some(line) = graph_line(text) {
            if line.listed.is_some() {
                Form::GraphListed(line)
            } else {
                Form::Graph(line)
            }
        } else if let Some(m) = group_re().captures(text) {
            Form::Group {
                group: m["group"].to_string(),
                finite: m.name("finite").is_some(),
                identity: m["identity"].to_string(),
            }
        } else if let Some(m) = set_or_point_re().captures(text) {
            if &m[2] == "set" {
                Form::Set(name(&m))
            } else {
                Form::Point(name(&m))
            }
        } else if let Some(m) = element_re().captures(text) {
            Form::Element(name(&m))
        } else if let Some(m) = property_re().captures(text) {
            Form::Property {
                name: name(&m),
                domain: m[2].to_string(),
            }
        } else if let Some(m) = function_on_re().captures(text) {
            Form::FunctionOn {
                name: name(&m),
                set: str::trim(&m[2]).to_string(),
            }
        } else if let Some(m) = polynomial_re().captures(text) {
            Form::Polynomial(name(&m))
        } else if let Some(m) = function_being_re().captures(text) {
            Form::FunctionBeing {
                typed: m[1].to_string(),
                being: m[2].to_string(),
            }
        } else if function_re().is_match(text) {
            Form::Function
        } else if let Some(m) = part_re().captures(text) {
            Form::Part {
                name: name(&m),
                whole: str::trim(&m[2]).to_string(),
            }
        } else if let Some(m) = not_in_re().captures(text) {
            Form::NotIn(name(&m))
        } else if membership_re().is_match(text) {
            Form::Member
        } else {
            Form::Other
        };
        Introduction { body, form }
    }

    /// The name the line introduces, which every form writes first; None
    /// where the line takes none of the forms.
    pub fn name(&self) -> Option<&str> {
        let first = |re: &regex::Regex| {
            re.captures(self.body.text())
                .and_then(|m| m.get(1))
                .map(|m| m.as_str())
        };
        match &self.form {
            Form::GraphListed(line) | Form::Graph(line) => Some(&line.graph),
            Form::Group { group, .. } => Some(group),
            Form::Set(name)
            | Form::Point(name)
            | Form::Element(name)
            | Form::Polynomial(name)
            | Form::NotIn(name)
            | Form::Property { name, .. }
            | Form::FunctionOn { name, .. }
            | Form::Part { name, .. } => Some(name),
            Form::FunctionBeing { .. } | Form::Function => first(function_re()),
            Form::Member => first(membership_re()),
            Form::Other => None,
        }
    }

    /// The parts of the line that are formula text, each as written: the
    /// whole of a membership, a thing not in a set and a function's type;
    /// otherwise the names it introduces and the sets and types it names,
    /// and none of its words.
    pub fn parts(&self) -> Vec<Written> {
        let texts: Vec<&str> = match &self.form {
            Form::Member | Form::NotIn(_) | Form::Function | Form::Other => {
                return vec![self.body.clone()];
            }
            Form::GraphListed(line) | Form::Graph(line) => {
                let mut out = vec![line.graph.as_str()];
                match &line.listed {
                    Some(l) => {
                        out.extend([l.vertex_set.as_str(), l.edge_set.as_str()]);
                        out.extend(l.joins.iter().map(|j| j.said.as_str()));
                    }
                    None => out.extend([line.vertices.as_str(), line.edges.as_str()]),
                }
                out
            }
            Form::Group {
                group, identity, ..
            } => vec![group, identity],
            Form::Set(name)
            | Form::Point(name)
            | Form::Element(name)
            | Form::Polynomial(name) => {
                vec![name]
            }
            Form::Property { name, domain } => vec![name, domain],
            Form::FunctionOn { name, set } => vec![name, set],
            Form::FunctionBeing { typed, .. } => vec![typed],
            Form::Part { name, whole } => vec![name, whole],
        };
        texts.into_iter().map(|t| self.part(t)).collect()
    }

    /// A part of the line that is formula text, with where it is written.
    pub fn part(&self, text: &str) -> Written {
        Written::new(text, self.body.path(), self.body.line())
    }

    /// One part of the line read as one formula.
    pub fn read_part(&self, text: &str, g: &Grammar, sorts: &Sorts) -> Checked<Node> {
        self.part(text).sentence()?.read(g, sorts)
    }

    /// What the line asserts, which a citation of it supplies: a membership
    /// and a function's type as written; `X ∈ 𝒫A` of a part, which is what
    /// `for all X ⊆ A` ranges over; what `be` says of a function, `f : A → B
    /// is one-to-one`; that a function is on its set, and a polynomial one;
    /// that a group is finite; of a graph given in full, its two sets, that
    /// the names in each differ, and which vertices each edge joins. A
    /// thing named of a sort, an element, a set, a point, a property, a
    /// group or a graph named and no more, asserts nothing.
    pub fn asserted(&self, g: &Grammar, sorts: &Sorts) -> Checked<Vec<Node>> {
        let read = |text: &str| self.read_part(text, g, sorts);
        Ok(match &self.form {
            Form::Member | Form::NotIn(_) | Form::Function | Form::Other => self
                .body
                .sentences()
                .iter()
                .map(|s| s.read(g, sorts))
                .collect::<Checked<Vec<Node>>>()?,
            Form::Part { name, whole } => {
                let (x, s) = (read(name)?, read(whole)?);
                vec![filled("x ∈ 𝒫S", g, sorts, &[("x", &x), ("S", &s)])?]
            }
            Form::FunctionOn { name, set } => {
                let (f, s) = (read(name)?, read(set)?);
                vec![filled(
                    "f is a function on S",
                    g,
                    sorts,
                    &[("f", &f), ("S", &s)],
                )?]
            }
            Form::Polynomial(name) => {
                let p = read(name)?;
                vec![filled("p is a polynomial", g, sorts, &[("p", &p)])?]
            }
            Form::FunctionBeing { typed, being } => {
                vec![self.being(typed, being, g, sorts)?]
            }
            Form::Group {
                group,
                finite: true,
                ..
            } => {
                let set = read(group)?;
                vec![filled("G is finite", g, sorts, &[("G", &set)])?]
            }
            Form::GraphListed(line) => {
                let Some(listing) = &line.listed else {
                    return Ok(Vec::new());
                };
                let mut said =
                    vec![read(&listing.vertex_set)?, read(&listing.edge_set)?];
                for list in [&listing.vertices, &listing.edges] {
                    for (i, one) in list.iter().enumerate() {
                        for other in &list[i + 1..] {
                            let (x, y) = (read(one)?, read(other)?);
                            said.push(filled(
                                "x ≠ y",
                                g,
                                sorts,
                                &[("x", &x), ("y", &y)],
                            )?);
                        }
                    }
                }
                for j in &listing.joins {
                    said.push(read(&j.said)?);
                }
                said
            }
            Form::Group { finite: false, .. }
            | Form::Graph(_)
            | Form::Set(_)
            | Form::Point(_)
            | Form::Element(_)
            | Form::Property { .. } => Vec::new(),
        })
    }

    /// What `be` says of a function with the type `typed`: the notation
    /// whose pattern is the type's with `is` and the words after `be`.
    fn being(
        &self,
        typed: &str,
        being: &str,
        g: &Grammar,
        sorts: &Sorts,
    ) -> Checked<Node> {
        let typed = self.read_part(typed, g, sorts)?;
        let pattern = format!("_ : _ → _ is {being}");
        made_as(g, &pattern, typed.children.clone()).ok_or_else(|| {
            crate::outcome::Problem::new(
                self.body.path(),
                self.body.line(),
                format!("`let … be {being}` says a function is something no notation says one is"),
            )
        })
    }
}

//! A `let` line's introduction, read once (`GRAMMAR.md`, an introduction
//! is not a formula).
//!
//! A `let` line names something and says what it is, in one of the forms
//! `GRAMMAR.md` lists. Which form is the skeleton's to read, word by word,
//! and the parts of a form that are formulas, a set or a function's type,
//! are formula text, read by the front end. What the line asserts is made
//! from those parts as trees (`asserted`), never written out as text and
//! parsed.

use crate::formula::page::{filled, made_as, Written};
use crate::formula::{Grammar, Node, Sorts};
use crate::outcome::Checked;

use super::{GraphLine, GraphListing, Joined};

/// What `text` writes after its first `n` words, from the next word on.
fn after_words(text: &str, n: usize) -> &str {
    let mut rest = text.trim_start();
    for _ in 0..n {
        let end = rest.find(char::is_whitespace).unwrap_or(rest.len());
        rest = rest[end..].trim_start();
    }
    rest
}

/// A line with a sign, `x ∈ A`: the one word before the sign, perhaps
/// written against it, and what follows it.
struct Signed<'t> {
    name: &'t str,
    after: &'t str,
}

/// The line read about its first `sign`; None for a line with no such
/// sign, more than one word before it, or nothing after it.
fn signed(text: &str, sign: char) -> Option<Signed<'_>> {
    let (name, after) = text.split_once(sign)?;
    let (name, after) = (name.trim(), after.trim());
    let one_word = !name.is_empty() && !name.contains(char::is_whitespace);
    (one_word && !after.is_empty()).then_some(Signed { name, after })
}

/// The name a function's type gives, `f : A → B`: one word before the
/// colon, and after it an arrow with something on either side; None for any
/// other line.
fn typed_name(text: &str) -> Option<&str> {
    let typed = signed(text, ':')?;
    let arrow = typed.after.rfind('→')?;
    let after = &typed.after[arrow + '→'.len_utf8()..];
    (arrow > 0 && !after.is_empty()).then_some(typed.name)
}

/// A function's type and what `be` says of it, `f : A → B be one-to-one`:
/// the type up to the first word `be` that follows a word after its arrow,
/// and the words after that `be`; None where the line has no such `be`.
fn typed_being(text: &str) -> Option<(&str, &str)> {
    typed_name(text)?;
    let colon = text.find(':')?;
    for (arrow, _) in text.rmatch_indices('→').filter(|&(at, _)| at > colon) {
        let rest = &text[arrow + '→'.len_utf8()..];
        for word in rest.split_whitespace().skip(1) {
            if word != "be" {
                continue;
            }
            let at = word.as_ptr() as usize - text.as_ptr() as usize;
            let being = text[at + word.len()..].trim_start();
            if !being.is_empty() {
                return Some((text[..at].trim_end(), being));
            }
        }
    }
    None
}

/// The graph a `let` body states, in either form; None for any other body,
/// or a listing one of whose clauses says no join.
pub fn graph_line(text: &str) -> Option<GraphLine> {
    let words: Vec<&str> = text.split_whitespace().collect();
    if let [graph, "be", "an", "undirected", "multigraph", "with", "vertices", vertices, "and", "edges", edges] =
        words[..]
    {
        return Some(GraphLine {
            graph: graph.to_string(),
            vertices: vertices.to_string(),
            edges: edges.to_string(),
            listed: None,
        });
    }
    let [graph, "be", "the", "undirected", "multigraph", "with", "distinct", "vertices", ..] =
        words[..]
    else {
        return None;
    };
    let vertices = listed_set(after_words(text, 8))?;
    let ["and", "distinct", "edges", ..] =
        vertices.after.split_whitespace().collect::<Vec<_>>()[..]
    else {
        return None;
    };
    let edges = listed_set(after_words(vertices.after, 3))?;
    let joins = edges.after.strip_prefix(',')?;
    let joins = after_words(joins, 0).strip_prefix("where")?;
    if !joins.starts_with(char::is_whitespace) || joins.trim().is_empty() {
        return None;
    }
    let mut joined = Vec::new();
    for clause in joins.trim().split(',') {
        let said = str::trim(clause);
        let [edge, "joins", first, "and", second] =
            said.split_whitespace().collect::<Vec<_>>()[..]
        else {
            return None;
        };
        joined.push(Joined {
            edge: edge.to_string(),
            first: first.to_string(),
            second: second.to_string(),
            said: said.to_string(),
        });
    }
    Some(GraphLine {
        graph: graph.to_string(),
        vertices: vertices.name.to_string(),
        edges: edges.name.to_string(),
        listed: Some(GraphListing {
            vertices: listed_names(vertices.list),
            edges: listed_names(edges.list),
            joins: joined,
            vertex_set: vertices.whole.to_string(),
            edge_set: edges.whole.to_string(),
        }),
    })
}

/// A set listed where a graph is given in full, `V = {A, B, C, D}`.
struct Listed<'t> {
    /// The set as the line writes it, a formula of its own.
    whole: &'t str,
    name: &'t str,
    /// What the braces hold.
    list: &'t str,
    /// What the line writes after the closing brace.
    after: &'t str,
}

/// The set listed at the start of `text`; None where it opens with none.
fn listed_set(text: &str) -> Option<Listed<'_>> {
    let close = text.find('}')?;
    let (name, list) = text[..close].split_once('=')?;
    let name = name.trim();
    let list = list.trim_start().strip_prefix('{')?;
    if name.is_empty() || name.contains(char::is_whitespace) {
        return None;
    }
    Some(Listed {
        whole: &text[..=close],
        name,
        list,
        after: &text[close + 1..],
    })
}

/// The names a listing writes, `A, B, C`.
fn listed_names(list: &str) -> Vec<String> {
    list.split(',').map(|n| str::trim(n).to_string()).collect()
}

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
        let form = Self::form_of(body.text());
        Introduction { body, form }
    }

    /// The form `text` takes, read word by word in the order the forms are
    /// tried: a graph or a group, which name several things; the forms
    /// with `be`; a function's type, with or without `be`; and the forms
    /// with a sign, ⊆, ∉ or ∈, whose name is all that stands before the
    /// sign.
    fn form_of(text: &str) -> Form {
        let words: Vec<&str> = text.split_whitespace().collect();
        if let Some(line) = graph_line(text) {
            return if line.listed.is_some() {
                Form::GraphListed(line)
            } else {
                Form::Graph(line)
            };
        }
        let [name, rest @ ..] = words.as_slice() else {
            return Form::Other;
        };
        let name = name.to_string();
        match rest {
            ["be", "a", "finite", "group", "with", "operation", _, "and", "identity", identity]
            | ["be", "a", "group", "with", "operation", _, "and", "identity", identity] => {
                return Form::Group {
                    group: name,
                    finite: rest[2] == "finite",
                    identity: identity.to_string(),
                }
            }
            ["be", "a", "set"] => return Form::Set(name),
            ["be", "a", "point"] => return Form::Point(name),
            ["be", "an", "element"] => return Form::Element(name),
            ["be", "a", "property", "of", "the", "elements", "of", domain] => {
                return Form::Property {
                    name,
                    domain: domain.to_string(),
                }
            }
            ["be", "a", "function", "on", _, ..] => {
                return Form::FunctionOn {
                    name,
                    set: after_words(text, 5).to_string(),
                }
            }
            ["be", "a", "polynomial"] => return Form::Polynomial(name),
            _ => {}
        }
        if let Some((typed, being)) = typed_being(text) {
            return Form::FunctionBeing {
                typed: typed.to_string(),
                being: being.to_string(),
            };
        }
        if typed_name(text).is_some() {
            return Form::Function;
        }
        if let Some(part) = signed(text, '⊆') {
            return Form::Part {
                name: part.name.to_string(),
                whole: part.after.to_string(),
            };
        }
        if let Some(not_in) = signed(text, '∉') {
            return Form::NotIn(not_in.name.to_string());
        }
        if signed(text, '∈').is_some() {
            return Form::Member;
        }
        Form::Other
    }

    /// The name the line introduces, which every form writes first; None
    /// where the line takes none of the forms.
    pub fn name(&self) -> Option<&str> {
        let text = self.body.text();
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
            Form::FunctionBeing { .. } | Form::Function => typed_name(text),
            Form::Member => signed(text, '∈').map(|member| member.name),
            Form::Other => None,
        }
    }

    /// The parts of the line that are formula text, each as written: the
    /// whole of a membership, a thing not in a set and a function's type;
    /// otherwise the names it introduces and the sets and types it names,
    /// and none of its words. These are all a reading of the line reads
    /// (`asserted_by`), so the checker reads each once and the build looks
    /// each up.
    pub fn parts(&self) -> Vec<Written> {
        let texts: Vec<&str> = match &self.form {
            Form::Member | Form::Function | Form::Other => {
                return vec![self.body.clone()];
            }
            Form::NotIn(name) => return vec![self.body.clone(), self.part(name)],
            Form::GraphListed(line) | Form::Graph(line) => {
                let mut out = vec![line.graph.as_str()];
                match &line.listed {
                    Some(l) => {
                        out.extend([l.vertex_set.as_str(), l.edge_set.as_str()]);
                        out.extend(l.vertices.iter().map(String::as_str));
                        out.extend(l.edges.iter().map(String::as_str));
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

    /// What the line asserts, which a citation of it supplies: a membership
    /// and a function's type as written; `X ∈ 𝒫A` of a part, which is what
    /// `for all X ⊆ A` ranges over; what `be` says of a function, `f : A → B
    /// is one-to-one`; that a function is on its set, and a polynomial one;
    /// that a group is finite; of a graph given in full, its two sets, that
    /// the names in each differ, and which vertices each edge joins. A
    /// thing named of a sort, an element, a set, a point, a property, a
    /// group or a graph named and no more, asserts nothing.
    pub fn asserted(&self, g: &Grammar, sorts: &Sorts) -> Checked<Vec<Node>> {
        self.asserted_by(&|part: &Written| part.formula()?.read(g, sorts), g, sorts)
    }

    /// `asserted`, each part of the line read by `reader`: the build's
    /// reader takes a part of its own page as the checker read it.
    pub fn asserted_by(
        &self,
        reader: &dyn Fn(&Written) -> Checked<Node>,
        g: &Grammar,
        sorts: &Sorts,
    ) -> Checked<Vec<Node>> {
        let read = |text: &str| reader(&self.part(text));
        Ok(match &self.form {
            Form::Member | Form::NotIn(_) | Form::Function | Form::Other => {
                vec![reader(&self.body)?]
            }
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
                vec![self.being(read(typed)?, being, g)?]
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

    /// What `be` says of a function with the type `typed`, read: the
    /// notation whose pattern is the type's with `is` and the words after
    /// `be`.
    fn being(&self, typed: Node, being: &str, g: &Grammar) -> Checked<Node> {
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

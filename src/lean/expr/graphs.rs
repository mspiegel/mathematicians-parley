//! The words of a graph: an edge joining two vertices, and a vertex
//! incident with an edge. The graph the theorem's `let` line names is the
//! function sending each edge to its two ends, `G : β → Sym2 α`, as set.mm's
//! iEdg is; every other notion of a graph is written out as its definition
//! says (`checker::written`).

use super::*;

/// The graph in scope: its letter and what its vertices and edges hold.
struct InScope {
    name: String,
    vertex: Members,
    edge: Members,
}

impl Writer<'_> {
    /// The one graph a `let` line names in scope; declined where none or
    /// more than one does, as the page's words of a graph name no graph.
    fn graph_in_scope(&self) -> Route<InScope> {
        let mut graphs = self.letters.iter().filter_map(|(name, ty)| match ty {
            LetterType::Graph { vertex, edge, .. } => Some(InScope {
                name: name.clone(),
                vertex: vertex.clone(),
                edge: edge.clone(),
            }),
            _ => None,
        });
        match (graphs.next(), graphs.next()) {
            (Some(g), None) => Route::Built(g),
            (None, _) => Route::no("a word of a graph where no line lets a graph"),
            (Some(_), Some(_)) => {
                Route::no("a word of a graph where two lines let one")
            }
        }
    }

    /// The two ends of an edge, `G a`.
    fn ends(&self, graph: &InScope, edge: &Node) -> Route<Printed> {
        self.element_term(edge, &graph.edge).map(|a| {
            Printed::of(
                super::super::doc::TermKind::App {
                    head: Box::new(Printed::letter(
                        super::super::names::letter(&graph.name),
                        LetterType::Graph {
                            vertices: String::new(),
                            edges: String::new(),
                            vertex: graph.vertex.clone(),
                            edge: graph.edge.clone(),
                        }
                        .lean_type(),
                    )),
                    args: vec![super::super::doc::Arg::Explicit(a)],
                    explicit: false,
                },
                LeanType::Sym2(Box::new(graph.vertex.member_type())),
            )
        })
    }

    /// a joins u and w: its ends are u and w, in either order, `G a =
    /// Sym2.mk u w`.
    pub(super) fn joins(&self, edge: &Node, u: &Node, w: &Node) -> Route<Printed> {
        let graph = match self.graph_in_scope() {
            Route::Built(g) => g,
            Route::Declined(d) => return Route::Declined(d),
        };
        let ends = match self.ends(&graph, edge) {
            Route::Built(e) => e,
            Route::Declined(d) => return Route::Declined(d),
        };
        let mut items = Vec::new();
        for v in [u, w] {
            match self.element_term(v, &graph.vertex) {
                Route::Built(p) => items.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        let unordered = Printed::applied(
            "Sym2.mk",
            super::super::doc::Source::Mathlib,
            items,
            LeanType::Sym2(Box::new(graph.vertex.member_type())),
        );
        relation_of("=", ends, unordered)
    }

    /// x is incident with a: x is one of its ends, `x ∈ G a`.
    pub(super) fn incident(&self, vertex: &Node, edge: &Node) -> Route<Printed> {
        let graph = match self.graph_in_scope() {
            Route::Built(g) => g,
            Route::Declined(d) => return Route::Declined(d),
        };
        match (
            self.element_term(vertex, &graph.vertex),
            self.ends(&graph, edge),
        ) {
            (Route::Built(x), Route::Built(ends)) => relation_of("∈", x, ends),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        }
    }
}

//! Which of a statement's sets hold things of one type: things two of its
//! terms compare, join or are members of are of one type, and a map takes
//! the things of its domain to those of the set it maps into, which are of
//! another where nothing the statement says makes them one. A pair, and a
//! product of sets, is made of things of two types the same way: X × Y
//! holds pairs of X's things and Y's.
//!
//! A backend whose sets are typed gives each type its own type variable:
//! the Lean writer reads it of an item's sentences, and of a theorem's
//! page from the checker's record (`CheckedTheorem::thing_types`).

use std::collections::{BTreeMap, BTreeSet};

use crate::formula::{Node, Sorts, Whole};
use crate::notations::{
    APPLICATION, BIJECTION, COMPOSITION, FOR_ALL, FUNCTIONS_FROM, FUNCTION_TYPE, IMAGE,
    INCIDENT, INVERSE, JOINS, ONE_TO_ONE, ONE_TO_ONE_ONTO, ONTO, PAIR, PRODUCT_SET,
    SET_BUILDER, SET_IMAGE, THERE_IS,
};

/// Whether the node is a letter the sorts make a map.
pub fn map_letter(node: &Node, sorts: Option<&Sorts>) -> bool {
    node.is_name()
        && matches!(
            sorts
                .and_then(|s| s.get(node.text.as_str()))
                .and_then(|s| s.full()),
            Some(Whole::Function(..))
        )
}

/// What a statement's things are of: a letter's own, or what a map letter
/// takes or gives.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ThingKey {
    /// The things a set, element or property letter is or holds or is of.
    Letter(String),
    /// What a map letter takes.
    From(String),
    /// What a map letter gives.
    To(String),
    /// The pairs a product or a pair term is or holds, by the order the
    /// lines meet such terms: X × Y and (a, b) each make one.
    Pairs(usize),
    /// What those pairs' first places hold.
    First(usize),
    /// What those pairs' second places hold.
    Second(usize),
}

/// What a letter's things are: of one type variable, or pairs of the
/// things of two (`ThingTypes::things_of_letter`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Things {
    Var(usize),
    Pairs(Box<Things>, Box<Things>),
}

/// The type variable a statement's things take, by what they are of. Of
/// `E : Y → Z` and `u ∈ {E(s) : s ∈ Y} ↔ there is s ∈ Y with u = E(s)`, Y
/// and s are α, Z and u are β; of `f : X → X`, all are α; of `(a, b) ∈ X ×
/// Y`, a and X are α, b and Y are β. Variables are numbered in the order
/// the lines first name their things.
#[derive(Clone, Debug, Default)]
pub struct ThingTypes {
    parent: BTreeMap<ThingKey, ThingKey>,
    /// Of each class of pairs, by its root, the keys of its two places: two
    /// classes of pairs joined join their places, place by place.
    places: BTreeMap<ThingKey, (ThingKey, ThingKey)>,
    /// How many product or pair terms the lines have met.
    pair_terms: usize,
    /// Each key, in the order first met.
    met: Vec<ThingKey>,
    vars: BTreeMap<ThingKey, usize>,
    /// The letters a "there is f : X → Y" binds, maps as a map letter of
    /// the sorts is.
    bound_maps: BTreeSet<String>,
}

impl ThingTypes {
    /// Read from the lines in order.
    pub fn read(sets: &[String], lines: &[&Node], sorts: Option<&Sorts>) -> ThingTypes {
        ThingTypes::read_given(sets, lines, &[], sorts)
    }

    /// Read from the lines in order, and from the values the page gives its
    /// own letters, each letter of one type with its value: X and A of
    /// `instantiate X := A in line 1`. `sets` are letters a line lets as sets
    /// without a formula, a graph's vertices and edges: each holds things
    /// of a type of its own where nothing joins it to another's, in the
    /// order given.
    pub fn read_given(
        sets: &[String],
        lines: &[&Node],
        given: &[(String, Node)],
        sorts: Option<&Sorts>,
    ) -> ThingTypes {
        let mut out = ThingTypes::default();
        for set in sets {
            out.meet(&ThingKey::Letter(set.clone()));
        }
        for line in lines {
            out.class(line, sorts);
        }
        for (letter, value) in given {
            let held = out.class(value, sorts);
            out.join(Some(ThingKey::Letter(letter.clone())), held);
        }
        // Things a letter is or holds are numbered first: a map's side that
        // no letter is of, the numbers of `v : {0, …, n} → V`, takes no
        // type variable before V's.
        let lettered: BTreeSet<ThingKey> = out
            .met
            .iter()
            .filter(|k| matches!(k, ThingKey::Letter(_)))
            .map(|k| out.root(k))
            .collect();
        let mut order: Vec<ThingKey> = out.met.clone();
        order.sort_by_key(|k| !lettered.contains(&out.root(k)));
        // A class of pairs takes no variable of its own: its places do.
        order.retain(|k| !out.places.contains_key(&out.root(k)));
        let mut roots: Vec<ThingKey> = Vec::new();
        for key in order {
            let root = out.root(&key);
            let var = match roots.iter().position(|r| *r == root) {
                Some(i) => i,
                None => {
                    roots.push(root);
                    roots.len() - 1
                }
            };
            out.vars.insert(key, var);
        }
        out
    }

    /// The type variable of these things; the first for any the lines do
    /// not name.
    pub fn var(&self, key: &ThingKey) -> usize {
        self.vars.get(key).copied().unwrap_or(0)
    }

    /// The type variable of a set, element or property letter's things.
    pub fn of_letter(&self, name: &str) -> usize {
        self.var(&ThingKey::Letter(name.to_string()))
    }

    /// What a set, element or property letter's things are: of one type
    /// variable, or pairs, S of `S ⊆ X × Y` pairs of X's things and Y's.
    pub fn things_of_letter(&self, name: &str) -> Things {
        self.things_of(&ThingKey::Letter(name.to_string()))
    }

    fn things_of(&self, key: &ThingKey) -> Things {
        match self.places.get(&self.root(key)) {
            Some((first, second)) => Things::Pairs(
                Box::new(self.things_of(first)),
                Box::new(self.things_of(second)),
            ),
            None => Things::Var(self.var(key)),
        }
    }

    fn root(&self, key: &ThingKey) -> ThingKey {
        let mut at = key.clone();
        while let Some(up) = self.parent.get(&at) {
            at = up.clone();
        }
        at
    }

    fn meet(&mut self, key: &ThingKey) {
        if !self.met.contains(key) {
            self.met.push(key.clone());
        }
    }

    /// The things of the two are of one type. Two classes of pairs joined
    /// join their first places and their second places; a class of pairs
    /// joined with any other makes its things pairs.
    fn join(&mut self, a: Option<ThingKey>, b: Option<ThingKey>) {
        let (Some(a), Some(b)) = (a, b) else {
            return;
        };
        self.meet(&a);
        self.meet(&b);
        let (ra, rb) = (self.root(&a), self.root(&b));
        if ra == rb {
            return;
        }
        self.parent.insert(rb.clone(), ra.clone());
        match (self.places.remove(&rb), self.places.get(&ra).cloned()) {
            (Some((f2, s2)), Some((f1, s1))) => {
                self.join(Some(f1), Some(f2));
                self.join(Some(s1), Some(s2));
            }
            (Some(places), None) => {
                self.places.insert(ra, places);
            }
            (None, _) => {}
        }
    }

    /// The key of the things a term is, holds or is made of, joining what
    /// the term says are of one type; None for a statement, a number or a
    /// map.
    fn class(&mut self, node: &Node, sorts: Option<&Sorts>) -> Option<ThingKey> {
        let bound = self.bound_maps.clone();
        let is_map = |n: &Node| {
            map_letter(n, sorts) || (n.is_name() && bound.contains(&*n.text))
        };
        let name = node.notation();
        let kids = node.children.as_slice();
        match (name, kids) {
            // An edge joins two vertices: the vertices are things of one
            // type, the edge of its own, as a graph's vertices and edges
            // are two sets.
            (JOINS, [a, u, w]) => {
                self.class(a, sorts);
                let (u, w) = (self.class(u, sorts), self.class(w, sorts));
                self.join(u, w);
                None
            }
            // A vertex incident with an edge: nothing joins the two.
            (INCIDENT, [x, a]) => {
                self.class(x, sorts);
                self.class(a, sorts);
                None
            }
            // There is f : X → Y with …, or {f ∈ the functions from X to Y :
            // …}: f a map from X's things to Y's, what the body says of it
            // read as of a map letter.
            (THERE_IS | FOR_ALL | SET_BUILDER, [f, set, body])
                if f.is_name() && set.notation() == FUNCTIONS_FROM =>
            {
                self.bound_maps.insert(f.text.to_string());
                if let [from, to] = set.children.as_slice() {
                    let (a, b) = (self.class(from, sorts), self.class(to, sorts));
                    self.join(Some(ThingKey::From(f.text.to_string())), a);
                    self.join(Some(ThingKey::To(f.text.to_string())), b);
                }
                self.class(body, sorts);
                None
            }
            _ if node.is_name() => {
                if is_map(node) || node.sort.is("number") || node.sort.is("formula") {
                    return None;
                }
                let key = ThingKey::Letter(node.text.to_string());
                self.meet(&key);
                Some(key)
            }
            // f : Y → Z, with or without a property, of a map letter, g ∘ f
            // or g⁻¹: the map takes Y's things to Z's (`sides`), so g ∘ f :
            // X → W puts X with f's side and W with g's, three types apart.
            (FUNCTION_TYPE | ONE_TO_ONE | ONTO | ONE_TO_ONE_ONTO, [f, from, to])
                if is_map(f) || matches!(f.notation(), COMPOSITION | INVERSE) =>
            {
                if let Some((takes, gives)) = self.sides(f, sorts) {
                    let (a, b) = (self.class(from, sorts), self.class(to, sorts));
                    self.join(Some(takes), a);
                    self.join(Some(gives), b);
                }
                None
            }
            // f(x), and f[X] the image: x and X are of what f takes, the
            // value of what it gives; under g⁻¹ the other way round.
            (APPLICATION | IMAGE, [f, x]) => {
                let arg = self.class(x, sorts);
                match self.sides(f, sorts) {
                    Some((takes, gives)) => {
                        self.join(Some(takes), arg);
                        Some(gives)
                    }
                    // P(t) of a property: t is of what P is of.
                    None if f.is_name() && !node.sort.is("number") => {
                        let p = self.class(f, sorts);
                        self.join(p, arg);
                        None
                    }
                    None => None,
                }
            }
            // A bijection from X to Y, or the maps from X to Y a "there is
            // f : X → Y" ranges over: X's things and Y's may be of two
            // types, as a map's sides are.
            (BIJECTION | FUNCTIONS_FROM, [from, to]) => {
                self.class(from, sorts);
                self.class(to, sorts);
                None
            }
            // X × Y holds pairs whose first places hold X's things and second
            // places Y's; (a, b) is a pair of a's things and b's. The two
            // places are of two types where nothing joins them, as a map's
            // sides are.
            (PRODUCT_SET | PAIR, [first, second]) => {
                let (a, b) = (self.class(first, sorts), self.class(second, sorts));
                let n = self.pair_terms;
                self.pair_terms += 1;
                let pairs = ThingKey::Pairs(n);
                self.places
                    .insert(pairs.clone(), (ThingKey::First(n), ThingKey::Second(n)));
                self.join(Some(ThingKey::First(n)), a);
                self.join(Some(ThingKey::Second(n)), b);
                Some(pairs)
            }
            // {E(s) : s ∈ Y}: s is of Y's things, and the set holds E(s)'s.
            (SET_IMAGE, [term, letter, set]) => {
                let (s, y) = (self.class(letter, sorts), self.class(set, sorts));
                self.join(s, y);
                self.class(term, sorts)
            }
            // A statement joins its terms, u = E(s), x ∈ X, ∀ x ∈ X; a
            // number is made of numbers; a term of sets, X ∪ Y, joins them.
            _ => {
                let classes: Vec<ThingKey> =
                    kids.iter().filter_map(|k| self.class(k, sorts)).collect();
                for pair in classes.windows(2) {
                    self.join(Some(pair[0].clone()), Some(pair[1].clone()));
                }
                let term = !node.sort.is("number") && !node.sort.is("formula");
                term.then(|| classes.into_iter().next()).flatten()
            }
        }
    }

    /// What a map term takes and gives: f's, g ∘ f's, or g⁻¹'s, the
    /// inverse taking what g gives back to what g takes; None for a term no
    /// map letter makes.
    fn sides(
        &mut self,
        f: &Node,
        sorts: Option<&Sorts>,
    ) -> Option<(ThingKey, ThingKey)> {
        if map_letter(f, sorts) || (f.is_name() && self.bound_maps.contains(&*f.text)) {
            let (from, to) = (
                ThingKey::From(f.text.to_string()),
                ThingKey::To(f.text.to_string()),
            );
            self.meet(&from);
            self.meet(&to);
            return Some((from, to));
        }
        match (f.notation(), f.children.as_slice()) {
            (INVERSE, [g]) => self.sides(g, sorts).map(|(a, b)| (b, a)),
            (COMPOSITION, [g, inner]) => {
                let (takes, mid) = self.sides(inner, sorts)?;
                let (mid2, gives) = self.sides(g, sorts)?;
                self.join(Some(mid), Some(mid2));
                Some((takes, gives))
            }
            _ => None,
        }
    }
}

//! A notation and a literal as small ids, compared as integers.
//!
//! A tree's node is of a notation, `equality`, and written with one of its
//! literals, `=` or `≠`. Every match and comparison asks which, at every
//! node, so each is an id: a notation's `NotationId`, and a literal's
//! `LiteralId`, its place among its notation's literals. The names and the
//! literals as written are kept once, in a registry for the process, which
//! a message, a printed tree and `Node::shape` read.
//!
//! The notations the code names have fixed ids, and the literals it names
//! fixed places (`crate::notations`), installed before any record is read,
//! so the code's consts are ids from the start and serve as `match`
//! patterns. Every other notation and literal a record declares is given the
//! next id as the grammar reads it. A name always has the same id, so two
//! grammars read in one process agree, and one with a notation the other
//! lacks only adds an id.

use std::sync::{Arc, OnceLock, RwLock};

use rustc_hash::FxHashMap;

/// A notation, by its id (`NotationId::of`, `name`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct NotationId(pub(crate) u16);

/// A literal's place among its notation's literals (`LiteralId::of`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct LiteralId(pub(crate) u8);

/// A notation and the literal it is written with: what tells `a < b` from
/// `a ≥ b`, both `order`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Spelling {
    pub notation: NotationId,
    pub literal: LiteralId,
}

/// The literal a node has where it is written with none: a letter, a
/// numeral, a term in kernel form, whose text is its own.
pub const NO_LITERAL: LiteralId = LiteralId(0);

/// A notation the code names, its fixed id and name, and the literals it
/// names, each at its fixed place (`crate::notations::KNOWN`).
pub struct Known {
    pub id: NotationId,
    pub name: &'static str,
    pub literals: &'static [(LiteralId, &'static str)],
}

struct Registry {
    names: Vec<Arc<str>>,
    by_name: FxHashMap<Arc<str>, NotationId>,
    /// Each notation's literals, by place.
    literals: Vec<Vec<Arc<str>>>,
}

impl Registry {
    /// The registry with the code's notations in it, each at its id.
    fn known() -> Registry {
        let mut out = Registry {
            names: Vec::new(),
            by_name: FxHashMap::default(),
            literals: Vec::new(),
        };
        for (at, known) in crate::notations::KNOWN.iter().enumerate() {
            assert_eq!(
                usize::from(known.id.0),
                at,
                "notation {} is at {at} in the table, and its id says {}",
                known.name,
                known.id.0
            );
            let id = out.add(known.name);
            for (place, (literal, text)) in known.literals.iter().enumerate() {
                assert_eq!(
                    usize::from(literal.0),
                    place + 1,
                    "literal {text} of {} is at {} in the table, and its id says {}",
                    known.name,
                    place + 1,
                    literal.0
                );
                out.literals[usize::from(id.0)].push(Arc::from(*text));
            }
        }
        out
    }

    fn add(&mut self, name: &str) -> NotationId {
        let id = NotationId(
            u16::try_from(self.names.len()).expect("fewer than 65536 notations"),
        );
        let name: Arc<str> = Arc::from(name);
        self.names.push(Arc::clone(&name));
        self.by_name.insert(name, id);
        // Place 0 is `NO_LITERAL`, the empty literal.
        self.literals.push(vec![Arc::from("")]);
        id
    }
}

fn registry() -> &'static RwLock<Registry> {
    static REGISTRY: OnceLock<RwLock<Registry>> = OnceLock::new();
    REGISTRY.get_or_init(|| RwLock::new(Registry::known()))
}

impl NotationId {
    /// The notation of this name, given an id the first time it is asked.
    pub fn of(name: &str) -> NotationId {
        if let Some(&id) = registry().read().expect("the registry").by_name.get(name) {
            return id;
        }
        let mut write = registry().write().expect("the registry");
        match write.by_name.get(name) {
            Some(&id) => id,
            None => write.add(name),
        }
    }

    /// The notation's name, as its record declares it.
    pub fn name(self) -> Arc<str> {
        let read = registry().read().expect("the registry");
        Arc::clone(&read.names[usize::from(self.0)])
    }
}

impl LiteralId {
    /// The literal `text` of `notation`, given a place the first time it is
    /// asked; the empty text is `NO_LITERAL`.
    pub fn of(notation: NotationId, text: &str) -> LiteralId {
        let at = usize::from(notation.0);
        let read = registry().read().expect("the registry");
        if let Some(id) = place_of(&read.literals[at], text) {
            return id;
        }
        drop(read);
        let mut write = registry().write().expect("the registry");
        if let Some(id) = place_of(&write.literals[at], text) {
            return id;
        }
        let all = &mut write.literals[at];
        all.push(Arc::from(text));
        LiteralId(u8::try_from(all.len() - 1).expect("fewer than 256 literals"))
    }
}

/// The place of the literal `text` among `all`, a notation's literals.
fn place_of(all: &[Arc<str>], text: &str) -> Option<LiteralId> {
    all.iter()
        .position(|l| &**l == text)
        .map(|p| LiteralId(u8::try_from(p).expect("fewer than 256 literals")))
}

impl Spelling {
    pub const fn new(notation: NotationId, literal: LiteralId) -> Spelling {
        Spelling { notation, literal }
    }

    /// The literal as written.
    pub fn text(self) -> Arc<str> {
        let read = registry().read().expect("the registry");
        Arc::clone(
            &read.literals[usize::from(self.notation.0)][usize::from(self.literal.0)],
        )
    }
}

//! The library a theorem is elaborated against.

use super::*;

/// What reading set.mm and the corpus's `proved.mm` gives. Nothing here
/// changes once read, so one is shared, between threads too, by every
/// [`Library`] built on it, and reading set.mm takes about a second.
pub struct ReadLibrary {
    /// set.mm and `proved.mm` together, held once and shared by every
    /// theorem, each of which adds its own labels in a [`Layered`] table.
    pub sigs: Arc<Signatures>,
    /// The labels `proved.mm` holds.
    pub provided: BTreeSet<String>,
    /// How many assertions set.mm holds, which the file header says.
    pub size: usize,
    /// set.mm's SHA-256, which the file header says.
    pub digest: String,
}

impl ReadLibrary {
    /// What set.mm's text and, where there is one, `proved.mm`'s give.
    pub fn from_texts(setmm: &str, proved: Option<&str>) -> ReadLibrary {
        let digest = {
            use sha2::{Digest, Sha256};
            Sha256::digest(setmm.as_bytes())
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect()
        };
        let provided: BTreeSet<String> = match proved {
            Some(p) => crate::mm::read_texts(&[p])
                .into_keys()
                .map(String::from)
                .collect(),
            None => BTreeSet::new(),
        };
        let mut texts = vec![setmm];
        texts.extend(proved);
        let sigs = crate::mm::read_texts(&texts);
        let size = sigs.len() - provided.len();
        ReadLibrary {
            sigs: Arc::new(sigs),
            provided,
            size,
            digest,
        }
    }
}

/// set.mm and the corpus's library, as every theorem of a build reads them:
/// what was read, shared, and the syntaxes this library has built, which are
/// its own. A syntax holds the terms it has spelt, and a term is built to be
/// read on one thread.
pub struct Library {
    pub(super) read: Arc<ReadLibrary>,
    /// The syntax the library gives with the corpus's constants declared,
    /// and every statement it has read, shared by every theorem elaborated
    /// against the same constants. A theorem reads the statements of the
    /// labels it uses, and reading them afresh for each theorem measured at
    /// four seconds of a ten-second build. Keyed by the constants, since a
    /// syntax holds for
    /// them alone and one library may serve corpora that declare others.
    pub(super) syntaxes: RefCell<IndexMap<Constants, Rc<Syntax>>>,
}

/// The labels a corpus declares on top of the library, with their
/// statements, in the order they are declared.
pub(super) type Constants = Vec<(Symbol, Vec<Symbol>)>;

impl std::ops::Deref for Library {
    type Target = ReadLibrary;

    fn deref(&self) -> &ReadLibrary {
        &self.read
    }
}

impl Library {
    /// The library read from set.mm and, where it has been built, the
    /// corpus's `proved.mm`.
    pub fn read(
        setmm: &std::path::Path,
        proved: Option<&std::path::Path>,
    ) -> Checked<Library> {
        let text = std::fs::read_to_string(setmm).map_err(|e| {
            Problem::new(
                setmm.display().to_string(),
                0,
                format!("cannot read set.mm: {e}"),
            )
        })?;
        let proved = match proved {
            Some(p) => Some(std::fs::read_to_string(p).map_err(|e| {
                Problem::new(p.display().to_string(), 0, e.to_string())
            })?),
            None => None,
        };
        Ok(Library::from_texts(&text, proved.as_deref()))
    }

    /// The library from set.mm's text and, where there is one, `proved.mm`'s.
    pub fn from_texts(setmm: &str, proved: Option<&str>) -> Library {
        Library::new(Arc::new(ReadLibrary::from_texts(setmm, proved)))
    }

    /// A library on what was read already, with syntaxes of its own.
    pub fn new(read: Arc<ReadLibrary>) -> Library {
        Library {
            read,
            syntaxes: RefCell::new(IndexMap::new()),
        }
    }

    /// What this library was read from, for another thread's library to be
    /// made on (`Library::new`).
    pub fn shared(&self) -> Arc<ReadLibrary> {
        Arc::clone(&self.read)
    }

    /// The syntax these signatures give, built once for each set of labels
    /// the corpus adds on top of the library.
    ///
    /// Only what a theorem adds before it reads anything may be added here:
    /// the corpus's constants. What it adds later (a step taken as stated, a
    /// lemma or hypothesis a library proof states) is never a syntax axiom,
    /// so the syntax built now is the one it would build itself.
    pub(super) fn syntax_for(&self, sigs: &Layered) -> Rc<Syntax> {
        let key: Constants = sigs
            .added()
            .map(|(label, sig)| (*label, sig.statement.clone()))
            .collect();
        if let Some(found) = self.syntaxes.borrow().get(&key) {
            return Rc::clone(found);
        }
        let made = Rc::new(Syntax::new(sigs));
        self.syntaxes.borrow_mut().insert(key, Rc::clone(&made));
        made
    }
}

/// The constants the corpus introduces, declared on the library: they are
/// not in it, so a notation that reaches one needs them declared before it is
/// read. They are the statements `definitions.mm` writes, built here rather
/// than read back from it.
pub(super) fn declare_constants(sigs: &mut Layered, records: &[Record]) -> Checked<()> {
    for one in super::super::definitions::definitions(records, sigs)? {
        let rendered = crate::mm::library::render(&one.body, sigs);
        let class = Symbol::of(&format!("c{}", one.token));
        let token = Symbol::of(&one.token);
        sigs.insert(
            class,
            Signature {
                label: class,
                kind: Kind::Axiom,
                statement: vec![Symbol::of("class"), token],
                floats: Vec::new(),
                essentials: Vec::new(),
                disjoint: BTreeSet::new(),
            },
        );
        let mut statement = vec![Symbol::of("|-"), token, Symbol::of("=")];
        statement.extend(rendered.split_whitespace().map(Symbol::of));
        let definition = Symbol::of(&format!("df-{}", one.token));
        sigs.insert(
            definition,
            Signature {
                label: definition,
                kind: Kind::Axiom,
                statement,
                floats: Vec::new(),
                essentials: Vec::new(),
                disjoint: BTreeSet::new(),
            },
        );
    }
    Ok(())
}

/// What an elaboration may be asked to do differently.
#[derive(Clone, Copy, Debug, Default)]
pub struct Options {
    /// The search offered every fact in scope, as it was before a step's
    /// proof was held to rest only on what the step names. Only the test of
    /// that rule turns it on, to see that the rule afterwards still catches
    /// what the search would have taken.
    pub whole_scope_offered: bool,
    /// Each sentence a step claims, said back from its kernel term as a
    /// message would say it and read again (`spoken`), with every sentence
    /// that comes back as another term kept in `Elaborated::said_back`.
    /// Only the test of what messages say turns it on.
    pub say_back: bool,
    /// The route proving a defined function's type from its rule
    /// (`map_into`) not taken. Only the test of gaps turns it on, to see a
    /// step the checker accepts and the build cannot prove reported as the
    /// build's to fix.
    pub map_types_off: bool,
}

/// One theorem's elaborated file, and the statement it proves, which a
/// theorem citing this one reads for the order of what it pushes.
pub struct Elaborated {
    pub text: String,
    pub statement: String,
    /// Where `Options::say_back` is on, each sentence said back as another
    /// term: the sentence, what it was said back as, and its line.
    pub said_back: Vec<String>,
}

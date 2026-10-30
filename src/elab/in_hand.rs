//! What a step, a requires line or a chain line's reason may use.
//!
//! A step's proof rests only on the lines the step names (R1), and a
//! requires line's or a chain line's only on what its reason names (R2).
//! `in_hand` makes that table once, where the proof starts: the facts in
//! scope that rest only on what the proof may rest on, and nothing else,
//! so that no route can reach a line the step does not name.
//!
//! The table keeps a link to the whole scope it was cut from, for what the
//! page says once and a proof may use without naming. The link is a
//! `Scope`, whose table only this file can read: what may be read through
//! it is written here, one function to a reason.

use std::collections::BTreeSet;
use std::rc::Rc;

use super::provenance::rests_within;
use super::state::Elaborator;
use super::Facts;
use crate::mm::spell::Proof;
use crate::mm::Rpn;
use crate::outcome::Checked;

/// The whole scope a narrowed table was cut from, carried with it to every
/// table made from it and widened with it (`Facts::rebased`), so that it
/// stands at the scope the table does.
#[derive(Clone)]
pub struct Scope(Rc<Facts>);

impl Scope {
    /// The whole scope, each proof carried as `carry` carries the narrowed
    /// table's.
    pub(super) fn rebased(&self, carry: &mut dyn FnMut(&Rpn, Proof) -> Proof) -> Scope {
        Scope(Rc::new(self.0.rebased(carry)))
    }
}

/// The whole scope behind `facts`: the table it was cut from where it was
/// narrowed (`in_hand`), and `facts` itself otherwise.
fn behind(facts: &Facts) -> Facts {
    match &facts.scope {
        Some(Scope(whole)) => Facts::clone(whole),
        None => facts.clone(),
    }
}

impl Elaborator<'_> {
    /// The facts the proof being built may use (`resting_on`): those in the
    /// scope `facts` was cut from whose proofs rest only on what it may rest
    /// on. Each line keeps its own proof as carried into the scope
    /// (`Facts::filtered_claims`), so that a line a requires line cites is
    /// read as it stands here. A requires line or a chain line narrows from
    /// the whole scope with what its step's table adds, not from that table
    /// alone, since its reason may name a line its step does not. Where
    /// nothing restricts the proof, it is the whole scope. The table is its
    /// own, so what a caller learns in it stays there.
    pub fn in_hand(&self, facts: &Facts) -> Facts {
        // What a route laid on the table it was handed, a step's requires
        // lines or what a cited line says, stands with the scope behind it.
        let whole = match &facts.scope {
            Some(Scope(behind)) => behind.with(facts),
            None => facts.clone(),
        };
        let mut named = match &self.resting {
            Some(allowed) => whole.filtered_claims(|_, p| rests_within(allowed, p)),
            None => whole.copy(),
        };
        named.scope = Some(Scope(Rc::new(whole)));
        named
    }

    /// What the `let` lines in scope say, named by the step or not, and
    /// nothing else: a function's type and the parts of a set, which a
    /// `let` says once (`citing::typed`), read where a declared type is
    /// widened to another codomain (`declared_type`).
    pub(super) fn said_by_lets(&self, facts: &Facts) -> Facts {
        behind(facts).filtered(|_, p| {
            !p.origin.is_empty() && p.origin.iter().all(|o| self.let_lines.contains(o))
        })
    }

    /// ( scope -> name = body ) from the define labelled `label`, its own
    /// line and nothing else, named by the step or not: a define says its
    /// function's type once, on its line (`map_into`), and the type is read
    /// through this equation.
    pub(super) fn define_equation(
        &mut self,
        name: &Rpn,
        body: &Rpn,
        label: &str,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let whole = behind(facts);
        let own = whole.filtered(|_, p| p.origin.iter().all(|o| o == label));
        self.held(&own, &crate::t!(name, body, "wceq"), scope)
    }

    /// ( scope -> -. a = b ) from anything in scope saying the two points
    /// differ, named or not: the page writes an angle only where its points
    /// are said to differ, and says it once (`citing::once`, an angle). What
    /// is read is `apart_held`'s; the result is sealed by the angle it is
    /// for (`angle_within`).
    pub(super) fn points_apart(
        &mut self,
        a: &Rpn,
        b: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let whole = behind(facts);
        self.resting_on(None::<BTreeSet<String>>, |me| {
            me.apart_held(a, b, scope, &whole)
        })
    }
}

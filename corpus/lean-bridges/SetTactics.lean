module

public import Lean.Parser.Command
public import Lean.Parser.Syntax
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Zify
public import Tactics

/-!
# What a page about sets leaves to its reader

`parley_side`, and after it the ways a goal about sets is closed: finite
sets compared or counted member by member, and a membership of a listed set
taken case by case. A generated file whose statements or steps use sets
calls `parley_set_side` where any other calls `parley_side`
(`build::lean`), so that a change here rebuilds only those files.
-/

public section

open Lean Meta Elab Tactic in
/-- "There is k with 0 ≤ k and P k", of a k a line says is at least 0 or
above 0, 0 ≤ k of `let k ∈ ℕ₀`: that k the witness, its fact the order,
and P k a line, cast as the goal is, L(k) = N(k)/10^k in ℚ for the goal's
ℝ. Each such fact is tried, the latest first. -/
elab "parley_witness_by_order" : tactic => withMainContext do
  let lines := (← getLCtx).decls.toList.filterMap id |>.filter (!·.isImplementationDetail)
  for line in lines.reverse do
    let said ← instantiateMVars line.type
    unless said.isAppOfArity ``LE.le 4 || said.isAppOfArity ``LT.lt 4 do continue
    let saved ← saveState
    try
      let x ← Term.exprToSyntax (said.getArg! 3)
      let h ← Term.exprToSyntax (mkFVar line.fvarId)
      evalTactic (← `(tactic| refine ⟨$x, $h, ?_⟩))
      for eq in lines.reverse do
        let inner ← saveState
        try
          let e ← Term.exprToSyntax (mkFVar eq.fvarId)
          Term.withoutErrToSorry (evalTactic (← `(tactic| exact_mod_cast $e)))
          if (← getGoals).isEmpty then return
        catch _ => pure ()
        inner.restore
    catch _ => pure ()
    saved.restore
  throwError "parley_witness_by_order: no fact 0 ≤ x in scope gives the witness"

/-- A set's count in ℕ∞, where the set is finite, is its count as a
natural number: what an item that counts in ℕ∞ says of a set a proof
counts as a natural number (`sets::count_term`). -/
theorem parley_encard_of_finite {α : Type*} {s : Set α} (h : s.Finite) :
    s.encard = (s.ncard : ℕ∞) := h.cast_ncard_eq.symm

/-- A part of a finite set is finite, the part asked first: `apply` then
finds the line that makes it a part, and the larger set is known. -/
theorem parley_finite_of_subset {α : Type*} {s t : Set α} (ht : t ⊆ s) (hs : s.Finite) :
    t.Finite := hs.subset ht

/-- The same of a member of the larger set's power set, W ∈ 𝒫 X, as
`obtain` gives the W of ∃ W ∈ 𝒫 X. -/
theorem parley_finite_of_mem_powerset {α : Type*} {s t : Set α} (ht : t ∈ 𝒫 s)
    (hs : s.Finite) : t.Finite := hs.subset ht

/-- The members of a finite set that have a property, {x ∈ A : P(x)}. -/
theorem parley_finite_sep {α : Type*} {s : Set α} {p : α → Prop} (hs : s.Finite) :
    {x | x ∈ s ∧ p x}.Finite := hs.subset fun _ h => h.1

/-- That a set is finite: a line says so, or gives its count as a number,
|X| = 2; it is ∅, listed or a range; it is made by ∖, ∩ or ∪ from finite
sets, or is the power set of one, {x ∈ A : …} or {E(s) : s ∈ A} of one;
or a line puts it inside a finite set, as a part or a member of its power
set. These are the sets the writer counts as natural numbers by how they
are made (`sets::is_finite`). -/
syntax "parley_finite" : tactic
macro_rules
  | `(tactic| parley_finite) => `(tactic| first
    | assumption
    | exact Set.toFinite _
    | (apply Set.finite_of_encard_eq_coe; assumption)
    | (apply Set.Finite.sdiff; parley_finite)
    | (apply Set.Finite.inter_of_left; parley_finite)
    | (apply Set.Finite.inter_of_right; parley_finite)
    | (apply Set.Finite.union <;> parley_finite)
    | (apply Set.Finite.powerset; parley_finite)
    | (apply parley_finite_sep; parley_finite)
    | (apply Set.Finite.image; parley_finite)
    | (apply parley_finite_of_subset; assumption; parley_finite)
    | (apply parley_finite_of_mem_powerset; assumption; parley_finite))

open Lean Meta Elab Tactic in
/-- Each count in ℕ∞, `s.encard`, standing outside every binder in the goal
or a line in scope, of a set `parley_finite` shows finite, rewritten as the
natural number it is, `↑s.ncard`. A count inside a binder, the |A ∖ c| of
{c | |A ∖ c| < |A ∩ c|}, is left as written: the writer prints such a set
the same way in every term it writes, a `linear_combination` coefficient
among them, which a rewrite inside would part from. An attempt at a set
that logs an error is undone with its error. -/
elab "parley_encard_closed" : tactic => withMainContext do
  let goal ← getMainGoal
  let mut types : Array Expr := #[← instantiateMVars (← goal.getType)]
  for h in ← getLocalHyps do
    types := types.push (← instantiateMVars (← inferType h))
  let found ← IO.mkRef (#[] : Array Expr)
  for t in types do
    t.forEach fun e => do
      if e.isAppOfArity ``Set.encard 2 && !e.hasLooseBVars then
        let s := e.appArg!
        unless (← found.get).contains s do found.modify (·.push s)
  for s in ← found.get do
    let saved ← saveState
    let hadErrors := (← Core.getMessageLog).hasErrors
    let m ← mkFreshExprMVar (← mkAppM ``Set.Finite #[s])
    let shown ← try
        let rest ← Tactic.run m.mvarId! (evalTactic (← `(tactic| parley_finite)))
        pure rest.isEmpty
      catch _ => pure false
    if !shown || (!hadErrors && (← Core.getMessageLog).hasErrors) then
      saved.restore
    else
      -- The set given as found: the proof's own type may have it in
      -- another form, A ∩ P for {x ∈ A : P(x)}, which is not found again.
      let eqn ← mkAppOptM ``parley_encard_of_finite #[none, some s, some (← instantiateMVars m)]
      -- One line at a time, the lines read again after each: replacing a
      -- line brings back each line after it under a new name.
      let mut g ← getMainGoal
      let mut rewritten := true
      while rewritten do
        rewritten := false
        let hyps ← g.withContext do
          return (← getLocalHyps).map (·.fvarId!)
        for h in hyps do
          let next ← g.withContext do
            try
              let r ← g.rewrite (← instantiateMVars (← h.getType)) eqn
              return some (← g.replaceLocalDecl h r.eNew r.eqProof).mvarId
            catch _ => return none
          if let some g2 := next then
            g := g2
            rewritten := true
            break
      g ← g.withContext do
        try
          let r ← g.rewrite (← instantiateMVars (← g.getType)) eqn
          g.replaceTargetEq r.eNew r.eqProof
        catch _ => return g
      replaceMainGoal [g]

/-- Each count in ℕ∞ of a finite set, in the goal and the lines in scope,
taken to the integer it is: k ≤ |W| to (k : ℤ) ≤ (W.ncard : ℤ). A step
that computes with counts a line or its claim says in ℕ∞, as set.mm's ♯
counts, computes with the integers (`theorem::count_conversion`). -/
macro "parley_count_int" : tactic => `(tactic|
  ((try parley_encard_closed);
   (try simp only [← Nat.cast_add, ← Nat.cast_mul, Nat.cast_inj, Nat.cast_le, Nat.cast_lt] at *);
   (try zify at *);
   -- A count said of an integer the page puts in ℕ₀, `↑m.toNat`: the
   -- integer itself, by its fact 0 ≤ m.
   (try simp (disch := omega) only [Int.toNat_of_nonneg] at *)))

/-- The other way, for a goal: a relation of integer counts of finite sets,
(|X ∪ Y| : ℤ) = m + n, said in ℕ∞, (X ∪ Y).encard = m + n, as an item
that counts in ℕ∞ says it. The goal's sets have their types where an
item's may not yet, ∅ of `card-empty`, so the item is then taken as it
stands (`theorem::close`). -/
macro "parley_count_ext" : tactic => `(tactic|
  (norm_cast;
   first
     | rw [← Nat.cast_inj (R := ℕ∞)]
     | rw [← Nat.cast_le (α := ℕ∞)]
     | rw [← Nat.cast_lt (α := ℕ∞)];
   push_cast; simp (disch := parley_finite) only [← parley_encard_of_finite]))

/-- A calculation or substitute rows, built as written, then what it built
and the goal both taken to integers (`parley_count_int`), so each meets the
other in the same words (`theorem::count_conversion`). -/
macro "parley_count_after " e:term : tactic =>
  `(tactic| (have hStep : _ := $e; parley_count_int; exact hStep))

/-- `parley_side`, then the ways of sets. -/
macro "parley_set_side" : tactic =>
  `(tactic| first
    -- Something said of every or some member of a set given by a property,
    -- the page's ℕ as {n : ℤ | 0 < n}, of a line that says it with the
    -- property beside the letter; a map into all of a type maps anything
    -- there. This and the next are tried before `parley_side`, whose last
    -- way, `simp_all`, recurses past Lean's limit beside a set a define
    -- builds and a line x = e(x), a = a·1 + b·0, which `first` does not
    -- recover from.
    | (simp only [Set.mem_ofPred_eq, Set.mem_univ, Set.mapsTo_univ, true_and, true_implies,
         forall_const];
       and_intros <;> first | assumption | omega | (exact ⟨_, ‹_›⟩) | (exact ⟨_, _, ‹_›⟩) | (exact ⟨_, _, rfl⟩) | parley_witness_by_order)
    -- A line of membership in a set given by a property within all of a
    -- type, {t ∈ ℝ : P t}, where the goal names the set by its letter.
    | (simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and] at *; assumption)
    -- There is some member of a set, of a member a line names.
    | (exact ⟨_, ‹_ ∈ _›, trivial⟩)
    -- A part a line says, Y ⊆ W, asked as a member of the power set,
    -- Y ∈ 𝒫W, or the other way round. Before `parley_side`, for the
    -- reason above.
    | (simp only [Set.mem_powerset_iff] at *; assumption)
    -- A count in ℕ∞ an item asks or gives, of a set the proof counts as a
    -- natural number, |A| = 0 of card-zero from (A.ncard : ℤ) = 0: each
    -- count of a finite set as that number, then the casts taken off.
    | (simp (disch := parley_finite) only [parley_encard_of_finite] at *;
       (try norm_cast at *);
       first | done | assumption | omega | (exact_mod_cast ‹_›))
    | parley_side
    -- Two finite sets of numbers equal, {x ∈ {−3, −2, 0, 5} : x is odd} =
    -- {−3, 5}: member by member, each case decided.
    | (ext x; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff];
       constructor <;> intro h <;> (try casesm* _ ∨ _, _ ∧ _) <;> (try subst_vars) <;>
       simp_all (config := {decide := true}); done)
    -- A count of a finite set the page lists or builds, |{1, 2}| = 2:
    -- counted as a Finset, each member decided.
    | (rw [Set.encard_eq_coe_toFinset_card];
       simp (config := {decide := true})
         [Set.toFinset_insert, Set.toFinset_singleton, Set.toFinset_setOf]; done)
    -- The same counted as a natural number, (|{1, 2}| : ℤ) = 2.
    | (norm_cast; rw [Set.ncard_eq_toFinset_card'];
       simp (config := {decide := true}); done)
    -- One of a listed set, x ∈ {a, b}, taken case by case.
    | (simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *;
       rcases ‹_ ∨ _› with h | h <;> simp [h]; done)
    -- One of a range of integers, x ∈ S with S = {3, …, 5}: its bounds,
    -- and the integers between them.
    | (subst_vars; simp only [Set.mem_Icc] at *; omega)
    -- A pair a line says, in the other order: {a, b} is {b, a}, a listed
    -- set's order being none of the page's.
    | (rw [Set.pair_comm]; assumption)
    -- A listed set a line puts inside another, in another order: each of
    -- its members, one of the line's.
    | (intro x hx; apply_assumption; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢;
        tauto)
    -- A map's value at a member of its domain, f(a) > 0 of f : ℕ → ℕ:
    -- the page's ℕ is the integers above 0, which a natural a is among.
    | (simp only [Set.MapsTo, Set.mem_ofPred_eq] at *; apply_assumption; omega))

module

public import Mathlib
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

/-- `parley_side`, then the ways of sets. -/
macro "parley_set_side" : tactic =>
  `(tactic| first
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
    -- One of a listed set, x ∈ {a, b}, taken case by case.
    | (simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *;
       rcases ‹_ ∨ _› with h | h <;> simp [h]; done)
    -- One of a range of integers, x ∈ S with S = {3, …, 5}: its bounds,
    -- and the integers between them.
    | (subst_vars; simp only [Set.mem_Icc] at *; omega))

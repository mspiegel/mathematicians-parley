module

public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/textbook-exercise-shapes-two.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapesTwo.ALimitUnfoldedOnTheLine

theorem a_limit_unfolded_on_the_line (f : ℝ → ℝ) (c : ℝ) (L : ℝ) (hH4 : Filter.Tendsto f (nhdsWithin c ((Set.univ : Set ℝ) \ {c})) (nhds L)) :
    (∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε))) := by
  -- 1. def:limit-at D := ℝ, from H4
  have r93_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := c) (L := L))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := c) (L := L))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := c) (L := L))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := c) (L := L))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := c) (L := L))).mp (by parley_set_side); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.TextbookExerciseShapesTwo.ALimitUnfoldedOnTheLine

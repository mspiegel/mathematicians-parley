module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/elaborator/a-limit-of-a-define-on-a-part.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ALimitOfADefineOnAPart.ALimitOfADefineOnAnOpenInterval

theorem a_limit_of_a_define_on_an_open_interval (a : ℝ) (b : ℝ) (c : ℝ) (L : ℝ) (h : ℝ → ℝ) (hH5 : Set.MapsTo h (Set.Ioo a b : Set ℝ) (Set.univ : Set ℝ)) (k : ℝ → ℝ) (hD1 : ∀ x : ℝ, x ∈ (Set.Ioo a b : Set ℝ) → k x = h x + 1) (hH6 : (Set.Ioo a b : Set ℝ) ⊆ (Set.univ : Set ℝ)) (hH7 : Set.MapsTo k (Set.Ioo a b : Set ℝ) (Set.univ : Set ℝ)) (hH8 : Filter.Tendsto k (nhdsWithin c ((Set.Ioo a b : Set ℝ) \ {c})) (nhds L)) :
    (∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.Ioo a b : Set ℝ), x ≠ c ∧ abs (x - c) < δ → abs (k x - L) < ε))) := by
  -- 1. def:limit-at D := (a, b), f := k, from H6, H7, H8
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.Ioo a b : Set ℝ), x ≠ c ∧ abs (x - c) < δ → abs (k x - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := k) (D := (Set.Ioo a b : Set ℝ)) hH6 (c := c) (L := L))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Calculus.def_limit_at (f := k) (D := (Set.Ioo a b : Set ℝ)) hH6 (c := c) (L := L))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_limit_at (f := k) (D := (Set.Ioo a b : Set ℝ)) hH6 (c := c) (L := L))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_limit_at (f := k) (D := (Set.Ioo a b : Set ℝ)) hH6 (c := c) (L := L))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := k) (D := (Set.Ioo a b : Set ℝ)) hH6 (c := c) (L := L))).mp (by parley_set_side); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ALimitOfADefineOnAPart.ALimitOfADefineOnAnOpenInterval

module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from proofs/hammack/limit-unique.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LimitUnique.LimitUnfolded

theorem limit_unfolded (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (f : ℝ → ℝ) (hH2 : Set.MapsTo f D (Set.univ : Set ℝ)) (c : ℝ) (L : ℝ) (hH5 : Filter.Tendsto f (nhdsWithin c (D \ {c})) (nhds L)) :
    (∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε))) := by
  -- 1. def:limit-at, from H1, H5
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := D) hH1 (c := c) (L := L))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := D) hH1 (c := c) (L := L))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := D) hH1 (c := c) (L := L))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := D) hH1 (c := c) (L := L))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := D) hH1 (c := c) (L := L))).mp (by parley_set_side); parley_set_side)
  all_goals exact s1

end Parley.Proofs.Hammack.LimitUnique.LimitUnfolded

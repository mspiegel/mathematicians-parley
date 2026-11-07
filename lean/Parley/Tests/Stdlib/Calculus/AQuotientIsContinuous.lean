module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AQuotientIsContinuous

theorem a_quotient_is_continuous (E : Set ℝ) (hH1 : E ⊆ (Set.univ : Set ℝ)) (h : ℝ → ℝ) (hH2 : Set.MapsTo h E (Set.univ : Set ℝ)) (k : ℝ → ℝ) (hH3 : Set.MapsTo k E (Set.univ : Set ℝ)) (H : ℝ → ℝ) (hH4 : Set.MapsTo H E (Set.univ : Set ℝ)) (hH5 : ∀ y ∈ E, k y ≠ 0) (hH6 : ∀ y ∈ E, H y = h y / k y) (hH7 : ContinuousOn h E) (hH8 : ContinuousOn k E) :
    ContinuousOn H E := by
  -- 1. thm:continuous-quotient D := E, F := H, f := h, g := k, from H1, H5, H6, H7, H8
  have s1 : ContinuousOn H E := by first | exact (Parley.Items.Stdlib.Calculus.thm_continuous_quotient (F := H) (f := h) (g := k) (D := E) hH1 (by parley_set_side) (by parley_set_side) hH7 hH8) | exact ((Parley.Items.Stdlib.Calculus.thm_continuous_quotient (F := H) (f := h) (g := k) (D := E) hH1 (by parley_set_side) (by parley_set_side) hH7 hH8)).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_continuous_quotient (F := H) (f := h) (g := k) (D := E) hH1 (by parley_set_side) (by parley_set_side) hH7 hH8) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_continuous_quotient (F := H) (f := h) (g := k) (D := E) hH1 (by parley_set_side) (by parley_set_side) hH7 hH8) | (have h := (Parley.Items.Stdlib.Calculus.thm_continuous_quotient (F := H) (f := h) (g := k) (D := E) hH1 (by parley_set_side) (by parley_set_side) hH7 hH8); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.AQuotientIsContinuous

module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AMultipleIsContinuous

theorem a_multiple_is_continuous (E : Set ℝ) (hH1 : E ⊆ (Set.univ : Set ℝ)) (h : ℝ → ℝ) (hH2 : Set.MapsTo h E (Set.univ : Set ℝ)) (H : ℝ → ℝ) (hH3 : Set.MapsTo H E (Set.univ : Set ℝ)) (hH4 : ∀ y ∈ E, H y = 7 * h y) (hH5 : ContinuousOn h E) :
    ContinuousOn H E := by
  -- 1. thm:continuous-scaled D := E, c := 7, F := H, f := h, from H1, H4, H5
  exact (Parley.Items.Stdlib.Calculus.thm_continuous_scaled (F := H) (f := h) (D := E) hH1 (c := (7 : ℝ)) (by parley_set_side) hH5)

end Parley.Tests.Stdlib.Calculus.AMultipleIsContinuous

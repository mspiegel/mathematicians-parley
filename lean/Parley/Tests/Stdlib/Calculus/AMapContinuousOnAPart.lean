module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AMapContinuousOnAPart

theorem a_map_continuous_on_a_part (E : Set ℝ) (hH1 : E ⊆ (Set.univ : Set ℝ)) (T : Set ℝ) (hH2 : T ⊆ E) (h : ℝ → ℝ) (hH3 : Set.MapsTo h E (Set.univ : Set ℝ)) (hH4 : ContinuousOn h T) :
    ContinuousOn (fun y : ℝ => h y) T := by
  -- 1. mun:map-continuous-on-part D := E, S := T, f := h, from H1, H2, H4
  exact (Parley.Items.Stdlib.Calculus.mun_map_continuous_on_part (f := h) (D := E) (S := T) hH1 hH2 hH4)

end Parley.Tests.Stdlib.Calculus.AMapContinuousOnAPart

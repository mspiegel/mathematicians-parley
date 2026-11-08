module

public import SetTactics
public import Tactics
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

namespace Parley.Tests.Stdlib.Calculus.AConstantIsContinuous

theorem a_constant_is_continuous (E : Set ℝ) (hH1 : E ⊆ (Set.univ : Set ℝ)) (h : ℝ → ℝ) (hH2 : Set.MapsTo h E (Set.univ : Set ℝ)) (hH3 : ∀ y ∈ E, h y = 5) :
    ContinuousOn h E := by
  -- 1. thm:continuous-constant D := E, c := 5, g := h, from H1, H3
  exact (Parley.Items.Stdlib.Calculus.thm_continuous_constant (g := h) (D := E) hH1 (c := (5 : ℝ)) (by parley_set_side))

end Parley.Tests.Stdlib.Calculus.AConstantIsContinuous

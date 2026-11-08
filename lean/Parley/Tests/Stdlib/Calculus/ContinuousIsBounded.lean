module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ContinuousIsBounded

theorem continuous_is_bounded (c : ℝ) (d : ℝ) (h : ℝ → ℝ) (hH3 : Set.MapsTo h (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH4 : ContinuousOn h (Set.Icc c d : Set ℝ)) :
    (∃ M : ℝ, ∀ y ∈ (Set.Icc c d : Set ℝ), abs (h y) ≤ M) := by
  -- 1. thm:continuous-bounded a := c, b := d, f := h, from H4
  exact (Parley.Items.Stdlib.Calculus.thm_continuous_bounded (f := h) (a := c) (b := d) hH4)

end Parley.Tests.Stdlib.Calculus.ContinuousIsBounded

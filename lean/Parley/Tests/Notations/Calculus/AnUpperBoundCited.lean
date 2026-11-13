module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.AnUpperBoundCited

theorem an_upper_bound_cited :
    (∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1) := by
  -- 1. thm:one-bounds-the-unit-interval
  exact Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval.one_bounds_the_unit_interval

end Parley.Tests.Notations.Calculus.AnUpperBoundCited

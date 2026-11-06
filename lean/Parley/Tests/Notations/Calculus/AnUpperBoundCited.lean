module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.AnUpperBoundCited

theorem an_upper_bound_cited :
    (∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1) := by
  -- 1. thm:one-bounds-the-unit-interval
  have s1 : ∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1 := by first | exact Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval.one_bounds_the_unit_interval | exact (Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval.one_bounds_the_unit_interval).symm | simpa using Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval.one_bounds_the_unit_interval | exact_mod_cast Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval.one_bounds_the_unit_interval | (have h := Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval.one_bounds_the_unit_interval; parley_set_side)
  all_goals exact s1

end Parley.Tests.Notations.Calculus.AnUpperBoundCited

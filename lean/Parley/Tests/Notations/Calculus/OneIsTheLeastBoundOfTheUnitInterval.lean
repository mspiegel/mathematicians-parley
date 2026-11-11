module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Calculus
public import Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval
public import Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.OneIsTheLeastBoundOfTheUnitInterval

theorem one_is_the_least_bound_of_the_unit_interval :
    ((∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1) ∧ (∀ u : ℝ, (∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ u) → 1 ≤ u)) := by
  -- 1. thm:one-bounds-the-unit-interval
  have s1 : ∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1 := by exact Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval.one_bounds_the_unit_interval
  -- 2. thm:one-is-in-the-unit-interval
  have s2 : (1 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval.one_is_in_the_unit_interval
  -- 3. proof
  have s3 : ∀ u : ℝ, (∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ u) → 1 ≤ u := by
    intro u
    intro hA1
    -- 3.1. def:upper-bound S := [0, 1], from A1
    have s3_1 : ∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ u := by parley_set_side
    -- 3.2. instantiate s := 1 in line 3.1, from 2
    exact (s3_1 (1 : ℝ) s2)
  -- 4. join 1, 3
  have s4 : (∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1) ∧ (∀ u : ℝ, (∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ u) → 1 ≤ u) := by parley_set_side
  -- 5. def:least-upper-bound c := 1, S := [0, 1], from 4
  parley_set_side

end Parley.Tests.Notations.Calculus.OneIsTheLeastBoundOfTheUnitInterval

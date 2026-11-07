module

public import ArithTactics
public import SetTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Calculus
public import Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.AHalfDoesNotBoundTheUnitInterval

theorem a_half_does_not_bound_the_unit_interval :
    ¬ (∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1 / 2) := by
  -- 1. thm:one-is-in-the-unit-interval
  have s1 : (1 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval.one_is_in_the_unit_interval | exact (Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval.one_is_in_the_unit_interval).symm | simpa using Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval.one_is_in_the_unit_interval | exact_mod_cast Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval.one_is_in_the_unit_interval | (have h := Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval.one_is_in_the_unit_interval; parley_set_side)
  -- 2. contradiction
  have s2 : ¬ (∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1 / 2) := by
    by_contra hc_hS
    have hS : ∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1 / 2 := by parley_suppose hc_hS
    -- 2.1. def:upper-bound u := 1/2, S := [0, 1], from S
    have s2_1 : ∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1 / 2 := by parley_set_side
    -- 2.2. instantiate s := 1 in line 2.1, from 1
    have s2_2 : (1 : ℚ) ≤ 1 / 2 := by first | linarith [(s2_1 (1 : ℝ) (by parley_set_side))] | (have h := (s2_1 (1 : ℝ) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s2_1 (1 : ℝ) (by parley_set_side)) | (have h := (s2_1 (1 : ℝ) (by parley_set_side)); parley_set_side)
    exact absurd s2_2 (by norm_num)
    all_goals parley_set_side
  all_goals exact s2

end Parley.Tests.Notations.Calculus.AHalfDoesNotBoundTheUnitInterval

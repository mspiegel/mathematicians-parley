module

public import ArithTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-requires-line-adding-what-the-checker-added.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARequiresLineAddingWhatTheCheckerAdded.ARequiresLineAddingWhatTheCheckerAdded

theorem a_requires_line_adding_what_the_checker_added (p : ℝ) (hH2 : p > 0) (hH3 : ∃ n : ℤ, 0 < n ∧ (n : ℝ) > 2 / p) :
    (∃ n : ℤ, 0 < n ∧ 1 / (n : ℝ) ≤ 1 / (2 / p)) := by
  -- 1. mun:quotient-positive x := 2, y := p, from H2
  have r14_1 : (2 : ℤ) > 0 := by parley_arith
  have s1 : 2 / p > 0 := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 : ℝ)) (y := p) (by parley_side) (by parley_side))
  -- 2. obtain m from H3
  obtain ⟨m, s2a, s2b⟩ := hH3
  -- 3. inequalities
  have r21_1 : p ≠ 0 := by parley_side
  have s3 : (m : ℝ) ≥ 2 / p := by parley_order
  -- 4. mun:reciprocal-order x := 2/p, y := m, from 3
  have r27_1 : 2 / p > 0 := by parley_side
  have r27_2 : m > 0 := by parley_order
  have r27_3 : p ≠ 0 := by parley_side
  have s4 : 1 / (m : ℝ) ≤ 1 / (2 / p) := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 2 / p) (by parley_side) (y := (m : ℝ)) (by parley_side))).mp s3
  -- 5. exhibit, from 4
  exact ⟨m, s2a, s4⟩

end Parley.Tests.Elaborator.ARequiresLineAddingWhatTheCheckerAdded.ARequiresLineAddingWhatTheCheckerAdded

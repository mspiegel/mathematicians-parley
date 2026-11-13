module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-requires-line-adding-what-the-checker-added.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARequiresLineAddingWhatTheCheckerAdded.ARequiresLineAddingWhatTheCheckerAdded

theorem a_requires_line_adding_what_the_checker_added (p : ℝ) (hH2 : p > 0) (hH3 : ∃ n : ℤ, 0 < n ∧ (n : ℝ) > 2 / p) :
    (∃ n : ℤ, 0 < n ∧ 1 / (n : ℝ) ≤ 1 / (2 / p)) := by
  -- 1. mun:quotient-positive x := 2, y := p, from H2
  have r14_1 : (2 : ℤ) > 0 := by parley_arith
  have s1 : 2 / p > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 : ℝ)) (y := p) (by norm_num) hH2)
  -- 2. obtain m from H3
  obtain ⟨m, s2a, s2b⟩ := hH3
  -- 3. inequalities
  have r21_1 : p ≠ 0 := ne_of_gt (by linarith only [hH2])
  have s3 : (m : ℝ) ≥ 2 / p := by linarith only [s2b]
  -- 4. mun:reciprocal-order x := 2/p, y := m, from 3
  have r27_1 : 2 / p > 0 := by exact s1
  have r27_2 : m > 0 := by linarith only [s2a]
  have r27_3 : p ≠ 0 := ne_of_gt (by linarith only [hH2])
  have s4 : 1 / (m : ℝ) ≤ 1 / (2 / p) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 2 / p) r27_1 (y := (m : ℝ)) (by exact_mod_cast gt_iff_lt.mp r27_2))).mp s3
  -- 5. exhibit, from 4
  exact ⟨m, s2a, s4⟩

end Parley.Tests.Elaborator.ARequiresLineAddingWhatTheCheckerAdded.ARequiresLineAddingWhatTheCheckerAdded

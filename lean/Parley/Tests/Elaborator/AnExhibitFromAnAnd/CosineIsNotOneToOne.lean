module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/an-exhibit-from-an-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnExhibitFromAnAnd.CosineIsNotOneToOne

theorem cosine_is_not_one_to_one :
    (∃ x : ℝ, ∃ y : ℝ, x ≠ y ∧ Real.cos x = Real.cos y) := by
  -- 1. real arithmetic
  have s1 : Real.cos (0 : ℝ) = Real.cos (2 * Real.pi) := by
    have hv1 : Real.cos (2 * Real.pi) = 1 := by rw [congrArg Real.cos (show 2 * Real.pi = 0 + ((1 : ℤ) : ℝ) * (2 * Real.pi) by ring1), Real.cos_add_int_mul_two_pi, Real.cos_zero]
    have hv2 : Real.cos (0 : ℝ) = 1 := by rw [Real.cos_zero]
    linear_combination (-1) * hv1 + hv2
  -- 2. real arithmetic
  have s2 : 0 < 2 * Real.pi := by
    have hf1 : 3 < Real.pi := Real.pi_gt_three
    have hf2 : Real.pi < 4 := Real.pi_lt_four
    linarith only [hf1, hf2]
  -- 3. inequalities
  have s3 : 0 ≠ 2 * Real.pi := ne_of_lt (by linarith only [s2])
  -- 4. exhibit, from 1, 3
  exact ⟨(0 : ℝ), 2 * Real.pi, ⟨s3, s1⟩⟩

end Parley.Tests.Elaborator.AnExhibitFromAnAnd.CosineIsNotOneToOne

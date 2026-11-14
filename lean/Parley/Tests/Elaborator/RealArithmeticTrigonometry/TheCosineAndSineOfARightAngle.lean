module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.TheCosineAndSineOfARightAngle

theorem the_cosine_and_sine_of_a_right_angle :
    Real.cos (Real.pi / 2) = 0 ∧ Real.sin (Real.pi / 2) = 1 := by
  -- 1. real arithmetic
  have s1a : Real.cos (Real.pi / 2) = 0 := by
    have hv1 : Real.cos (Real.pi / 2) = -(0) := by rw [congrArg Real.cos (show Real.pi / 2 = 0 + Real.pi / 2 by ring1), Real.cos_add_pi_div_two, Real.sin_zero]
    linear_combination hv1
  have s1b : Real.sin (Real.pi / 2) = 1 := by
    have hv1 : Real.sin (Real.pi / 2) = 1 := by rw [congrArg Real.sin (show Real.pi / 2 = 0 + Real.pi / 2 by ring1), Real.sin_add_pi_div_two, Real.cos_zero]
    linear_combination hv1
  exact ⟨s1a, s1b⟩

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.TheCosineAndSineOfARightAngle

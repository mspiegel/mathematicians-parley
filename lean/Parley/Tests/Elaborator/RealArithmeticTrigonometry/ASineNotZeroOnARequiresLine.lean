module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineNotZeroOnARequiresLine

theorem a_sine_not_zero_on_a_requires_line (a : ℝ) :
    a * Real.sin (Real.pi / 3) / Real.sin (Real.pi / 3) = a := by
  -- 1. algebra
  have r91_1 : Real.sin (Real.pi / 3) ≠ 0 := by
    have hv1 : Real.sin (Real.pi / 3) = Real.sqrt (3 : ℝ) / 2 := by rw [congrArg Real.sin (show Real.pi / 3 = Real.pi / 3 by ring1), Real.sin_pi_div_three]
    have hr3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    intro h
    have h0 : (-(3 / 4 : ℝ) : ℝ) = 0 := (show (-(3 / 4 : ℝ) : ℝ) = 0 by linear_combination (-((1 / 2 : ℝ) * Real.sqrt (3 : ℝ))) * h + ((1 / 2 : ℝ) * Real.sqrt (3 : ℝ)) * hv1 + ((1 / 4 : ℝ)) * hr3)
    norm_num at h0
  have hz1 : Real.sin (Real.pi / 3) ≠ 0 := r91_1; field

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineNotZeroOnARequiresLine

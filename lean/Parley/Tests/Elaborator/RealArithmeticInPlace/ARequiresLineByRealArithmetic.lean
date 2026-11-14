module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-in-place.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticInPlace.ARequiresLineByRealArithmetic

theorem a_requires_line_by_real_arithmetic (a : ℝ) :
    a * (Real.sqrt (2 : ℝ) - 1) / (Real.sqrt (2 : ℝ) - 1) = a := by
  -- 1. algebra
  have r25_1 : Real.sqrt (2 : ℝ) - 1 ≠ 0 := by
    have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    intro h
    have h0 : (-1 : ℝ) = 0 := (show (-1 : ℝ) = 0 by linear_combination (-Real.sqrt (2 : ℝ) - 1) * h + hr2)
    norm_num at h0
  have hz1 : Real.sqrt (2 : ℝ) - 1 ≠ 0 := r25_1; field

end Parley.Tests.Elaborator.RealArithmeticInPlace.ARequiresLineByRealArithmetic

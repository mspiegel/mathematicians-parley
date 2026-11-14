module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
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
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic-in-place.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticInPlace.ALinkByRealArithmetic

theorem a_link_by_real_arithmetic :
    Real.sqrt (8 : ℝ) + Real.sqrt (2 : ℝ) = 3 * Real.sqrt (2 : ℝ) := by
  -- 1. calculation
  calc Real.sqrt (8 : ℝ) + Real.sqrt (2 : ℝ) = 2 * Real.sqrt (2 : ℝ) + Real.sqrt (2 : ℝ) := by
        have hv1 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt (2 : ℝ) := by rw [congrArg Real.sqrt (show (8 : ℝ) = 2 ^ 2 * 2 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by positivity) 2, Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
        linear_combination hv1
    _ = 3 * Real.sqrt (2 : ℝ) := by
        ring1

end Parley.Tests.Elaborator.RealArithmeticInPlace.ALinkByRealArithmetic

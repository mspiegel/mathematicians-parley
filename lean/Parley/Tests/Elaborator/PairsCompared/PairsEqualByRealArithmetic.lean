module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/pairs-compared.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PairsCompared.PairsEqualByRealArithmetic

theorem pairs_equal_by_real_arithmetic :
    ((Real.sqrt (4 : ℝ), (1 : ℤ)) : ℝ × ℤ) = ((2 : ℝ), (1 : ℤ)) := by
  -- 1. real arithmetic
  exact Prod.ext (show Real.sqrt (4 : ℝ) = 2 by
    have hv1 : Real.sqrt (4 : ℝ) = 2 := by rw [congrArg Real.sqrt (show (4 : ℝ) = 2 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
    linear_combination hv1) (show (1 : ℤ) = 1 by
    ring1)

end Parley.Tests.Elaborator.PairsCompared.PairsEqualByRealArithmetic

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

/-! Written from tests/elaborator/pairs-compared.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PairsCompared.PairsApartByRealArithmetic

theorem pairs_apart_by_real_arithmetic :
    ¬ (((0 : ℤ), Real.sqrt (3 : ℝ)) : ℤ × ℝ) = ((0 : ℤ), (0 : ℝ)) := by
  -- 1. real arithmetic
  exact fun h => (show Real.sqrt (3 : ℝ) ≠ 0 by
    have hr3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    intro h
    have h0 : (-3 : ℝ) = 0 := (show (-3 : ℝ) = 0 by linear_combination (-Real.sqrt (3 : ℝ)) * h + hr3)
    norm_num at h0) (congrArg Prod.snd h)

end Parley.Tests.Elaborator.PairsCompared.PairsApartByRealArithmetic

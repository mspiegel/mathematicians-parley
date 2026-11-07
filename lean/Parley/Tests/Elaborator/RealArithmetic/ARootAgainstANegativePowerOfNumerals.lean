module

public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootAgainstANegativePowerOfNumerals

theorem a_root_against_a_negative_power_of_numerals :
    Real.sqrt (2 : ℝ) ≠ 3 ^ (-1 : ℤ) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (2 : ℝ) ≠ 3 ^ (-1 : ℤ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ARootAgainstANegativePowerOfNumerals

module

public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.APowerWithHalvedCoefficients

theorem a_power_with_halved_coefficients :
    ((1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) / 2) ^ 6 = 81 / 4 + 55 / 4 * Real.sqrt (2 : ℝ) + 45 / 4 * Real.sqrt (3 : ℝ) + 33 / 4 * Real.sqrt (6 : ℝ) := by
  -- 1. real arithmetic
  have s1 : ((1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) / 2) ^ 6 = 81 / 4 + 55 / 4 * Real.sqrt (2 : ℝ) + 45 / 4 * Real.sqrt (3 : ℝ) + 33 / 4 * Real.sqrt (6 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.APowerWithHalvedCoefficients

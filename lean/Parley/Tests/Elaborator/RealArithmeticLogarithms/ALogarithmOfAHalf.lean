module

public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAHalf

theorem a_logarithm_of_a_half :
    Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by
  -- 1. real arithmetic
  parley_real

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAHalf

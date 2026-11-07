module

public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.RealSqrt

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ACosineOfAQuarterOfPi

theorem a_cosine_of_a_quarter_of_pi :
    Real.cos (Real.pi / 4) = Real.sqrt (2 : ℝ) / 2 := by
  -- 1. real arithmetic
  have s1 : Real.cos (Real.pi / 4) = Real.sqrt (2 : ℝ) / 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ACosineOfAQuarterOfPi

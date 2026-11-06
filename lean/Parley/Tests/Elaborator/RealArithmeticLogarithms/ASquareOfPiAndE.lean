module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ASquareOfPiAndE

theorem a_square_of_pi_and_e :
    (Real.pi + Real.exp 1) ^ 2 = Real.pi ^ 2 + 2 * Real.pi * Real.exp 1 + Real.exp 1 ^ 2 := by
  -- 1. real arithmetic
  have s1 : (Real.pi + Real.exp 1) ^ 2 = Real.pi ^ 2 + 2 * Real.pi * Real.exp 1 + Real.exp 1 ^ 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ASquareOfPiAndE

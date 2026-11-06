module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.PiBelowFour

theorem pi_below_four :
    Real.pi < 4 := by
  -- 1. real arithmetic
  have s1 : Real.pi < 4 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.PiBelowFour

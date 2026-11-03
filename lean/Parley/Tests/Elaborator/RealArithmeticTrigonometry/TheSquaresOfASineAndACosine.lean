module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.TheSquaresOfASineAndACosine

theorem the_squares_of_a_sine_and_a_cosine :
    Real.sin (Real.pi / 6) ^ 2 + Real.cos (Real.pi / 6) ^ 2 = 1 := by
  -- 1. real arithmetic
  have s1 : Real.sin (Real.pi / 6) ^ 2 + Real.cos (Real.pi / 6) ^ 2 = 1 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.TheSquaresOfASineAndACosine

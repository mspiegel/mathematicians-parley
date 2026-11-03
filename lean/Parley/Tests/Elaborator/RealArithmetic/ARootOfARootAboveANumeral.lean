module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootOfARootAboveANumeral

theorem a_root_of_a_root_above_a_numeral :
    Real.sqrt (Real.sqrt (16 : ℝ)) > 1 := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (Real.sqrt (16 : ℝ)) > 1 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ARootOfARootAboveANumeral

module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootBelowANumeral

theorem a_root_below_a_numeral :
    Real.sqrt (4 : ℝ) < 3 := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (4 : ℝ) < 3 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ARootBelowANumeral

module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootOfASumWithARoot

theorem a_root_of_a_sum_with_a_root :
    Real.sqrt (1 + Real.sqrt (9 : ℝ)) = 2 := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (1 + Real.sqrt (9 : ℝ)) = 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ARootOfASumWithARoot

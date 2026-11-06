module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.AQuotientOfRootsThatIsWhole

theorem a_quotient_of_roots_that_is_whole :
    Real.sqrt (12 : ℝ) / Real.sqrt (3 : ℝ) = 2 := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (12 : ℝ) / Real.sqrt (3 : ℝ) = 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.AQuotientOfRootsThatIsWhole

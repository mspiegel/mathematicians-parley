module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.AQuotientOfRootsThatIsNotWhole

theorem a_quotient_of_roots_that_is_not_whole :
    ¬ (∃ m : ℤ, (m : ℝ) = Real.sqrt (2 : ℝ) / Real.sqrt (8 : ℝ)) := by
  -- 1. real arithmetic
  have s1 : ¬ (∃ m : ℤ, (m : ℝ) = Real.sqrt (2 : ℝ) / Real.sqrt (8 : ℝ)) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.AQuotientOfRootsThatIsNotWhole

module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootThatIsWhole

theorem a_root_that_is_whole :
    (∃ m : ℤ, 0 < m ∧ (m : ℝ) = Real.sqrt (4 : ℝ)) := by
  -- 1. real arithmetic
  have s1 : ∃ m : ℤ, 0 < m ∧ (m : ℝ) = Real.sqrt (4 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ARootThatIsWhole

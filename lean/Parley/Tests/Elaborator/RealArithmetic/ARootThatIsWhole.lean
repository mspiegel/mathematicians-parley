module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootThatIsWhole

theorem a_root_that_is_whole :
    (∃ m : ℕ, 0 < m ∧ (m : ℝ) = Real.sqrt (4 : ℝ)) := by
  -- 1. real arithmetic
  have s1 : ∃ m : ℕ, 0 < m ∧ (m : ℝ) = Real.sqrt (4 : ℝ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.ARootThatIsWhole

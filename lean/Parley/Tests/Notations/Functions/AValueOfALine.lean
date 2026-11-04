module

public import Tactics

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.AValueOfALine

theorem a_value_of_a_line (f : ℝ → ℝ) (hD1 : ∀ x : ℝ, f x = 2 * x + 1) :
    f 3 = 7 := by
  -- 1. D1
  have s1 : f 3 = 2 * 3 + 1 := by (try simp only [hD1]); first | done | parley_side
  -- 2. calculation
  have s2 : f 3 = 7 := by
    calc f 3 = 2 * 3 + 1 := by parley_side
      _ = 7 := by norm_num
  all_goals exact s2

end Parley.Tests.Notations.Functions.AValueOfALine

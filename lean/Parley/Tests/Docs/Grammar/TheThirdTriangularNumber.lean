module

public import Tactics

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.TheThirdTriangularNumber

theorem the_third_triangular_number :
    (3 * (3 + 1) / 2 : ℚ) = 6 := by
  -- 1. calculation
  have s1 : (3 * (3 + 1) / 2 : ℚ) = 6 := by
    calc (3 * (3 + 1) / 2 : ℚ) = 3 * (3 + 1) / 2 := by parley_side
      _ = 6 := by norm_num
  all_goals exact s1

end Parley.Tests.Docs.Grammar.TheThirdTriangularNumber

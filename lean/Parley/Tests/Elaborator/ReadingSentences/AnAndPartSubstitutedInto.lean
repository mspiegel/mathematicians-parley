module

public import LeanBridges

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartSubstitutedInto

theorem an_and_part_substituted_into (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ a < b) (hH4 : b = 2) :
    a < 2 := by
  -- 1. substitute b = 2 (H4) into H3
  have s1 : a < 2 := by parley_subst_at hH4 hH3
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartSubstitutedInto

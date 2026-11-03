module

public import Tactics

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWaySubstitutedInto

theorem a_congruence_the_other_way_substituted_into (a : ℤ) (b : ℤ) (c : ℤ) (n : ℕ) (hH4 : 0 < n) (hH5 : b ≡ a [ZMOD (n : ℤ)]) (hH6 : a = c) :
    c ≡ b [ZMOD (n : ℤ)] := by
  -- 1. substitute a = c (H6) into H5
  have s1 : c ≡ b [ZMOD (n : ℤ)] := by parley_subst_at hH6 hH5
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWaySubstitutedInto

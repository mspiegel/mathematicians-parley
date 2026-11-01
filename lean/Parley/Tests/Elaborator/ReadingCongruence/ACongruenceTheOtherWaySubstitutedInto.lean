module

public import Parley.Library

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWaySubstitutedInto

theorem a_congruence_the_other_way_substituted_into (a : ℤ) (b : ℤ) (c : ℤ) (n : ℕ) (H4 : 0 < n) (H5 : b ≡ a [ZMOD (n : ℤ)]) (H6 : a = c) :
    c ≡ b [ZMOD (n : ℤ)] := by
  -- 1. substitute a = c (H6) into H5
  have s1 : c ≡ b [ZMOD (n : ℤ)] := by parley_subst_at H6 H5
  parley_side

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWaySubstitutedInto

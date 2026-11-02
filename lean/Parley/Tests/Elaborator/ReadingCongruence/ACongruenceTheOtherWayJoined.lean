module

public import Tactics

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayJoined

theorem a_congruence_the_other_way_joined (a : ℤ) (b : ℤ) (n : ℕ) (hH3 : 0 < n) (hH4 : b ≡ a [ZMOD (n : ℤ)]) :
    a ≡ b [ZMOD (n : ℤ)] := by
  -- 1. restate H4
  have s1 : a ≡ b [ZMOD (n : ℤ)] := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayJoined

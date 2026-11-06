module

public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayJoined

theorem a_congruence_the_other_way_joined (a : ℤ) (b : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : b ≡ a [ZMOD n]) :
    a ≡ b [ZMOD n] := by
  -- 1. restate H4
  have s1 : a ≡ b [ZMOD n] := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayJoined

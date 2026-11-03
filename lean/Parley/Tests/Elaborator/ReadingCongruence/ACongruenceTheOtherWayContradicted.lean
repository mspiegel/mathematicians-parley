module

public import Tactics

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayContradicted

theorem a_congruence_the_other_way_contradicted (a : ℤ) (b : ℤ) (n : ℕ) (hH3 : 0 < n) (hH4 : b ≡ a [ZMOD (n : ℤ)]) :
    a ≡ b [ZMOD (n : ℤ)] := by
  -- 1. contradiction
  have s1 : a ≡ b [ZMOD (n : ℤ)] := by
    by_contra hc_hS
    have hS : ¬ a ≡ b [ZMOD (n : ℤ)] := by parley_suppose hc_hS
    -- 1.1. restate S
    have s1_1 : ¬ a ≡ b [ZMOD (n : ℤ)] := by parley_side
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayContradicted

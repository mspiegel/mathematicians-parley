module

public import Parley.Library

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayContradicted

theorem a_congruence_the_other_way_contradicted (a : ℤ) (b : ℤ) (n : ℕ) (H3 : 0 < n) (H4 : b ≡ a [ZMOD (n : ℤ)]) :
    a ≡ b [ZMOD (n : ℤ)] := by
  -- 1. contradiction
  have s1 : a ≡ b [ZMOD (n : ℤ)] := by
    by_contra hc_S
    have S : ¬ a ≡ b [ZMOD (n : ℤ)] := by parley_suppose hc_S
    -- 1.1. restate S
    have s1_1 : ¬ a ≡ b [ZMOD (n : ℤ)] := by parley_side
    parley_side
  parley_side

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayContradicted

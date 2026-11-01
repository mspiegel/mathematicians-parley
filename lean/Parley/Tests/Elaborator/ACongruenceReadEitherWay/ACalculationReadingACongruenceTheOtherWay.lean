module

public import Parley.Library

/-! Written from tests/elaborator/a-congruence-read-either-way.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACalculationReadingACongruenceTheOtherWay

theorem a_calculation_reading_a_congruence_the_other_way (a : ℤ) (b : ℤ) (c : ℤ) (n : ℕ) (H4 : 0 < n) (H5 : a ≡ b [ZMOD (n : ℤ)]) (H6 : c ≡ b [ZMOD (n : ℤ)]) :
    a ≡ c [ZMOD (n : ℤ)] := by
  -- 1. calculation
  have s1 : a ≡ c [ZMOD (n : ℤ)] := by
    calc a ≡ b [ZMOD (n : ℤ)] := by parley_side
      _ ≡ c [ZMOD (n : ℤ)] := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACalculationReadingACongruenceTheOtherWay

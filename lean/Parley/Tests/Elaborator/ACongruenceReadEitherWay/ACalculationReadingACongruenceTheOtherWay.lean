module

public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/a-congruence-read-either-way.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACalculationReadingACongruenceTheOtherWay

theorem a_calculation_reading_a_congruence_the_other_way (a : ℤ) (b : ℤ) (c : ℤ) (n : ℤ) (hH4 : 0 < n) (hH5 : a ≡ b [ZMOD n]) (hH6 : c ≡ b [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  -- 1. calculation
  have s1 : a ≡ c [ZMOD n] := by
    calc a ≡ b [ZMOD n] := by parley_side
      _ ≡ c [ZMOD n] := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACalculationReadingACongruenceTheOtherWay

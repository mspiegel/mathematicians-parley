module

public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/a-for-all-line-read-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineInACalculationLink

theorem a_for_all_line_in_a_calculation_link (n : ℤ) (hH1 : 0 < n) (c : ℤ) (hH3 : c ≡ (1 : ℤ) [ZMOD n]) (hH4 : ∀ x : ℤ, x ≡ c [ZMOD n]) :
    (∀ b : ℤ, b ≡ (1 : ℤ) [ZMOD n]) := by
  -- 1. proof
  have s1 : ∀ b : ℤ, b ≡ (1 : ℤ) [ZMOD n] := by
    intro b
    -- 1.1. calculation
    have s1_1 : b ≡ (1 : ℤ) [ZMOD n] := by
      calc b ≡ c [ZMOD n] := by parley_side
        _ ≡ 1 [ZMOD n] := by parley_side
    all_goals exact s1_1
  all_goals exact s1

end Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineInACalculationLink

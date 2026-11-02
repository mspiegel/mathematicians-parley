module

public import LeanBridges

/-! Written from tests/elaborator/a-for-all-line-read-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineInACalculationLink

theorem a_for_all_line_in_a_calculation_link (n : ℕ) (hH1 : 0 < n) (c : ℤ) (hH3 : c ≡ (1 : ℤ) [ZMOD (n : ℤ)]) (hH4 : ∀ x : ℤ, x ≡ c [ZMOD (n : ℤ)]) :
    (∀ b : ℤ, b ≡ (1 : ℤ) [ZMOD (n : ℤ)]) := by
  -- 1. proof
  have s1 : ∀ b : ℤ, b ≡ (1 : ℤ) [ZMOD (n : ℤ)] := by
    intro b
    -- 1.1. calculation
    have s1_1 : b ≡ (1 : ℤ) [ZMOD (n : ℤ)] := by
      calc b ≡ c [ZMOD (n : ℤ)] := by parley_side
        _ ≡ 1 [ZMOD (n : ℤ)] := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineInACalculationLink

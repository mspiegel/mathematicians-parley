module

public import LeanBridges

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInstantiated

theorem a_for_all_line_instantiated (hH1 : ∀ x : ℝ, ∀ z : ℝ, x * z = z * x) :
    (∀ y : ℝ, y * 2 = 2 * y) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, y * 2 = 2 * y := by
    intro y
    -- 1.1. instantiate z := 2 in H1
    have s1_1 : y * 2 = 2 * y := by first | linear_combination (norm := parley_norm) (hH1 y (2 : ℝ)) | (have h := (hH1 y (2 : ℝ)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (hH1 y (2 : ℝ)) | exact_mod_cast ((hH1 y (2 : ℝ))).symm | (have h := (hH1 y (2 : ℝ)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH1 y (2 : ℝ)); qify; linear_combination (norm := parley_norm) h)
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInstantiated

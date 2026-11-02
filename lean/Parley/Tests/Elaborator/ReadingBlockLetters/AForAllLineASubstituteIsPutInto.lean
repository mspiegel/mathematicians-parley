module

public import LeanBridges

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineASubstituteIsPutInto

theorem a_for_all_line_a_substitute_is_put_into (b : ℝ) (hH2 : ∀ x : ℝ, x ^ 2 ≥ 0) :
    (∀ y : ℝ, y = b → b ^ 2 ≥ 0) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, y = b → b ^ 2 ≥ 0 := by
    intro y
    intro hA1
    -- 1.1. substitute y = b (A1) into H2
    have s1_1 : b ^ 2 ≥ 0 := by parley_subst_at hA1 hH2
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineASubstituteIsPutInto

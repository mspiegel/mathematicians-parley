module

public import Tactics

/-! Written from tests/elaborator/a-hypothesis-over-a-define-restated.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AHypothesisOverADefineRestated.AHypothesisOverADefineRestated

theorem a_hypothesis_over_a_define_restated (n : ℕ) (hH2 : (∫ t in 0..1, (t ^ n / (1 + t ^ 2) : ℝ)) = 0) :
    (∫ t in 0..1, (t ^ n / (1 + t ^ 2) : ℝ)) = 0 := by
  -- 1. restate H2
  have s1 : (∫ t in 0..1, (t ^ n / (1 + t ^ 2) : ℝ)) = 0 := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.AHypothesisOverADefineRestated.AHypothesisOverADefineRestated

module

public import Tactics

/-! Written from tests/elaborator/a-sum-of-many-lines-by-inequalities.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumOfManyLinesByInequalities.ASumOfThreeBoundsOfTwoSentences

theorem a_sum_of_three_bounds_of_two_sentences (P : ℝ) (Q : ℝ) (R : ℝ) (M : ℝ) (hH5 : P > 0 ∧ P > M) (hH6 : Q > 0 ∧ Q ≥ 0) (hH7 : R > 0 ∧ R ≥ 0) :
    P + Q + R > M := by
  -- 1. inequalities, from H5, H6, H7
  have s1 : P + Q + R > M := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.ASumOfManyLinesByInequalities.ASumOfThreeBoundsOfTwoSentences

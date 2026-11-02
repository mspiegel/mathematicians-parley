module

public import Tactics

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInstantiated

theorem a_second_sentence_instantiated (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : ∀ x : ℝ, x * 0 = 0) :
    b * 0 = 0 := by
  -- 1. instantiate x := b in H3
  have s1 : b * 0 = 0 := by first | linear_combination (norm := parley_norm) (hH3b b) | (have h := (hH3b b); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH3b b); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH3b b) | exact_mod_cast ((hH3b b)).symm | (have h := (hH3b b); rify; linear_combination (norm := parley_norm) h) | (have h := (hH3b b); qify; linear_combination (norm := parley_norm) h) | (have h := (hH3b b); parley_int_power h) | (have h := (hH3b b); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInstantiated

module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceUnfolded

theorem a_second_sentence_unfolded (a : ℝ) (b : ℤ) (H3a : a = 1) (H3b : Even b) :
    (∃ k : ℤ, b = 2 * k) := by
  -- 1. def:even n := b, from H3
  have s1 : ∃ k : ℤ, b = 2 * k := by simpa using ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side)
  parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceUnfolded

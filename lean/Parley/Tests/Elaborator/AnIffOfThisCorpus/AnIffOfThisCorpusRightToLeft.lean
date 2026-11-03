module

public import Tactics
public import Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated

/-! Written from tests/elaborator/an-iff-of-this-corpus.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIffOfThisCorpus.AnIffOfThisCorpusRightToLeft

theorem an_iff_of_this_corpus_right_to_left (a : ℤ) (hH2 : a = 0) :
    (0 : ℤ) ∣ a := by
  -- 1. thm:zero-divides-restated n := a, from H2
  have s1 : (0 : ℤ) ∣ a := by first | (assumption; done) | exact ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mpr (by parley_side) | (have h := ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mpr (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.AnIffOfThisCorpus.AnIffOfThisCorpusRightToLeft

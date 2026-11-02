module

public import Tactics
public import Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated

/-! Written from tests/elaborator/an-iff-of-this-corpus.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIffOfThisCorpus.AnIffOfThisCorpusLeftToRight

theorem an_iff_of_this_corpus_left_to_right (a : ℤ) (hH2 : (0 : ℤ) ∣ a) :
    a = 0 := by
  -- 1. thm:zero-divides-restated n := a, from H2
  have s1 : a = 0 := by first | linear_combination (norm := parley_norm) ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mp (by parley_side) | (have h := ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mp (by parley_side) | exact_mod_cast (((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mp (by parley_side)).symm | (have h := ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mp (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mp (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mp (by parley_side); parley_int_power h) | (have h := ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mp (by parley_side); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.AnIffOfThisCorpus.AnIffOfThisCorpusLeftToRight

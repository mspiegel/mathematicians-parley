module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated

/-! Written from tests/elaborator/an-iff-of-this-corpus.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIffOfThisCorpus.AnIffOfThisCorpusLeftToRight

theorem an_iff_of_this_corpus_left_to_right (a : ℤ) (hH2 : (0 : ℤ) ∣ a) :
    a = 0 := by
  -- 1. thm:zero-divides-restated n := a, from H2
  exact ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mp hH2

end Parley.Tests.Elaborator.AnIffOfThisCorpus.AnIffOfThisCorpusLeftToRight

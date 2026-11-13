module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated

/-! Written from tests/elaborator/an-iff-of-this-corpus.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIffOfThisCorpus.AnIffOfThisCorpusRightToLeft

theorem an_iff_of_this_corpus_right_to_left (a : ℤ) (hH2 : a = 0) :
    (0 : ℤ) ∣ a := by
  -- 1. thm:zero-divides-restated n := a, from H2
  exact ((Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated.zero_divides_restated (n := a))).mpr hH2

end Parley.Tests.Elaborator.AnIffOfThisCorpus.AnIffOfThisCorpusRightToLeft

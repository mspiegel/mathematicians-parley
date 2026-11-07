module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/an-iff-of-this-corpus.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated

theorem zero_divides_restated (n : ℤ) :
    ((0 : ℤ) ∣ n ↔ n = 0) := by
  -- 1. mun:zero-divides
  have s1 : (0 : ℤ) ∣ n ↔ n = 0 := by exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n))
  all_goals exact s1

end Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated

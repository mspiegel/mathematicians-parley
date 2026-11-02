module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/an-iff-of-this-corpus.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated

theorem zero_divides_restated (n : ℤ) :
    ((0 : ℤ) ∣ n ↔ n = 0) := by
  -- 1. mun:zero-divides
  have s1 : (0 : ℤ) ∣ n ↔ n = 0 := by first | exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n)) | exact ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated

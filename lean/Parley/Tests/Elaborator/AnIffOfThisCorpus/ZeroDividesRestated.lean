module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/elaborator/an-iff-of-this-corpus.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated

theorem zero_divides_restated (n : ℤ) :
    ((0 : ℤ) ∣ n ↔ n = 0) := by
  -- 1. mun:zero-divides
  have s1 : (0 : ℤ) ∣ n ↔ n = 0 := by first | exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n)) | exact ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n))
  all_goals parley_side

end Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated

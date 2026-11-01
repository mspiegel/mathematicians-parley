module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialTwo

theorem binomial_two (m : ℕ) :
    (Parley.Library.choose (m : ℤ) (2 : ℤ) : ℚ) = (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  -- 1. mun:counting-binomial-two n := m
  have s1 : (Parley.Library.choose (m : ℤ) (2 : ℤ) : ℚ) = (m : ℚ) * ((m : ℚ) - 1) / 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_two (n := m))).symm
  all_goals parley_side

end Parley.Tests.Stdlib.Counting.BinomialTwo

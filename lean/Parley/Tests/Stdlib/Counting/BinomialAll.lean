module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialAll

theorem binomial_all (m : ℕ) :
    (Parley.Library.choose (m : ℤ) (m : ℤ) : ℤ) = 1 := by
  -- 1. mun:counting-binomial-all n := m
  have s1 : (Parley.Library.choose (m : ℤ) (m : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_all (n := m))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m)); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Stdlib.Counting.BinomialAll

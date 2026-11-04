module

public import Counting
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialTwo

theorem binomial_two (m : ℕ) :
    (LeanBridges.Counting.choose (m : ℤ) (2 : ℤ) : ℚ) = (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  -- 1. mun:counting-binomial-two n := m
  have s1 : (LeanBridges.Counting.choose (m : ℤ) (2 : ℤ) : ℚ) = (m : ℚ) * ((m : ℚ) - 1) / 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_two (n := m))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.BinomialTwo

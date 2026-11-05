module

public import Counting
public import FactorialTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialOne

theorem binomial_one (m : ℕ) :
    (LeanBridges.Counting.choose ((m : ℤ) + 1) (1 : ℤ) : ℤ) = (m : ℤ) + 1 := by
  -- 1. mun:counting-binomial-one n := m + 1
  have s1 : (LeanBridges.Counting.choose ((m : ℤ) + 1) (1 : ℤ) : ℤ) = (m : ℤ) + 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.BinomialOne

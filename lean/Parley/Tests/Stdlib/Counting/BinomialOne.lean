module

public import Counting
public import FactorialTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialOne

theorem binomial_one (m : ℤ) (hH1 : 0 ≤ m) :
    (LeanBridges.Counting.choose (m + 1) (1 : ℤ) : ℤ) = m + 1 := by
  -- 1. mun:counting-binomial-one n := m + 1
  have s1 : (LeanBridges.Counting.choose (m + 1) (1 : ℤ) : ℤ) = m + 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.BinomialOne

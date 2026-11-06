module

public import Counting
public import FactorialTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialAll

theorem binomial_all (m : ℤ) (hH1 : 0 ≤ m) :
    (LeanBridges.Counting.choose m m : ℤ) = 1 := by
  -- 1. mun:counting-binomial-all n := m
  have s1 : (LeanBridges.Counting.choose m m : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.BinomialAll

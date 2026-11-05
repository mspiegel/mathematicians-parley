module

public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.SizeOfARange

theorem size_of_a_range :
    ((Set.Icc (1 : ℤ) (12 : ℤ) : Set ℤ).ncard : ℤ) = 12 := by
  -- 1. mun:range-size n := 12
  have s1 : ((Set.Icc (1 : ℤ) (12 : ℤ) : Set ℤ).ncard : ℤ) = 12 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_range_size (n := 12)) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := 12)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := 12)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_range_size (n := 12)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_range_size (n := 12))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := 12)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := 12)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := 12)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := 12)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.SizeOfARange

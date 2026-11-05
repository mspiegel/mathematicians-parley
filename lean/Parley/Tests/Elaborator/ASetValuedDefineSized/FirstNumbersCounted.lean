module

public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/a-set-valued-define-sized.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted

theorem first_numbers_counted (m : ℕ) :
    ((Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ).ncard : ℤ) = (m : ℤ) := by
  -- 1. mun:range-size n := m, from D1
  have s1 : ((Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ).ncard : ℤ) = (m : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_range_size (n := m)) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_range_size (n := m)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_range_size (n := m))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted

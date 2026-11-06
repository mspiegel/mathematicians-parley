module

public import PowerTactics
public import SetTactics
public import Tactics
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.SizeOfARange

theorem size_of_a_range :
    (Set.Icc (1 : ℤ) (12 : ℤ) : Set ℤ).encard = ((12 : ℕ) : ℕ∞) := by
  -- 1. mun:range-size n := 12
  have s1 : (Set.Icc (1 : ℤ) (12 : ℤ) : Set ℤ).encard = ((12 : ℕ) : ℕ∞) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_range_size (n := (12 : ℤ)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := (12 : ℤ)) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := (12 : ℤ)) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_range_size (n := (12 : ℤ)) (by parley_set_side))) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_range_size (n := (12 : ℤ)) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_range_size (n := (12 : ℤ)) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := (12 : ℤ)) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := (12 : ℤ)) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := (12 : ℤ)) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := (12 : ℤ)) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.SizeOfARange

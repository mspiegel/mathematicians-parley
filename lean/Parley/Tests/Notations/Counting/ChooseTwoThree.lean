module

public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums
public import Parley.Library

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.ChooseTwoThree

theorem choose_two_three :
    (Parley.Library.choose (2 : ℤ) (3 : ℤ) : ℤ) = 0 := by
  -- 1. contradiction
  have s1 : ¬ (3 : ℤ) ∈ Finset.Icc (0 : ℤ) (2 : ℤ) := by
    by_contra hc_hS
    have hS : (3 : ℤ) ∈ Finset.Icc (0 : ℤ) (2 : ℤ) := by parley_suppose hc_hS
    -- 1.1. mun:range-bounds a := 0, b := 2, k := 3, from S
    have s1_1 : (3 : ℤ) ≤ 2 := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (2 : ℤ)) (k := (3 : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (2 : ℤ)) (k := (3 : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (2 : ℤ)) (k := (3 : ℤ)) (by parley_side))
    -- 1.2. arithmetic
    have s1_2 : ¬ (3 : ℤ) ≤ 2 := by parley_arith
    all_goals parley_side
  -- 2. mun:binomial-outside n := 2, k := 3, from 1
  have s2 : (Parley.Library.choose (2 : ℤ) (3 : ℤ) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := 2) (k := (3 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := 2) (k := (3 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := 2) (k := (3 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_outside (n := 2) (k := (3 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := 2) (k := (3 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := 2) (k := (3 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Notations.Counting.ChooseTwoThree

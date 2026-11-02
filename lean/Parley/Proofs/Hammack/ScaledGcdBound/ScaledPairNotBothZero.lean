module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/scaled-gcd-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ScaledGcdBound.ScaledPairNotBothZero

theorem scaled_pair_not_both_zero (x : ℤ) (y : ℤ) (c : ℤ) (hH4 : ¬ (x = 0 ∧ y = 0)) (hH5 : c ≠ 0) :
    ¬ (c * x = 0 ∧ c * y = 0) := by
  -- the theorem. contradiction
  have sThm : ¬ (c * x = 0 ∧ c * y = 0) := by
    by_contra hc_hS
    have hS : c * x = 0 ∧ c * y = 0 := by parley_suppose hc_hS
    -- 1. contradiction
    have s1 : x = 0 := by
      by_contra hc_hS1
      have hS1 : x ≠ 0 := by parley_suppose hc_hS1
      -- 1.1. mun:product-nonzero x := c, y := x, from H5, S1
      have s1_1 : c * x ≠ 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := x) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := x) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := x) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := x) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := x) (by parley_side) (by parley_side)); parley_side)
      all_goals parley_side
    -- 2. contradiction
    have s2 : y = 0 := by
      by_contra hc_hS2
      have hS2 : y ≠ 0 := by parley_suppose hc_hS2
      -- 2.1. mun:product-nonzero x := c, from H5, S2
      have s2_1 : c * y ≠ 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := y) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := y) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := y) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := y) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := y) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := y) (by parley_side) (by parley_side)); parley_side)
      all_goals parley_side
    -- 3. join 1, 2
    have s3 : x = 0 ∧ y = 0 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.ScaledGcdBound.ScaledPairNotBothZero

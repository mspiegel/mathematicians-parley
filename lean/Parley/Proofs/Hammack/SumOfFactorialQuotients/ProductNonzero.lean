module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/hammack/sum-of-factorial-quotients.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFactorialQuotients.ProductNonzero

theorem product_nonzero (x : ℝ) (y : ℝ) (hH3 : x ≠ 0) (hH4 : y ≠ 0) :
    x * y ≠ 0 := by
  -- the theorem. contradiction
  have sThm : x * y ≠ 0 := by
    by_contra hc_hS
    have hS : x * y = 0 := by parley_suppose hc_hS
    -- 1. algebra, from S
    have s1 : x * y = 0 * y := by linear_combination (norm := parley_norm) hS
    -- 2. mun:multiply-cancel a := x, b := 0, c := y, from H4, 1
    have s2 : x = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side))).symm
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.SumOfFactorialQuotients.ProductNonzero

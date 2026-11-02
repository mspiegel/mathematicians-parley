module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/divisors-not-zero-by-their-factors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.AProductDivisorBelowALineSayingIt

theorem a_product_divisor_below_a_line_saying_it (k : ℤ) (hH2 : k > 0) :
    (k * (k + 1) ≠ 0 ∧ 1 / (k : ℚ) - 1 / ((k : ℚ) + 1) = 1 / ((k : ℚ) * ((k : ℚ) + 1))) := by
  -- 1. inequalities, from H2
  have s1 : k + 1 > 0 := by parley_side
  -- 2. mun:product-nonzero x := k, y := k + 1
  have r46_1 : k ≠ 0 := by parley_side
  have r46_2 : k + 1 ≠ 0 := by parley_side
  have s2 : k * (k + 1) ≠ 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := k) (y := k + 1) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := k) (y := k + 1) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := k) (y := k + 1) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := k) (y := k + 1) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := k) (y := k + 1) (by parley_side) (by parley_side)); parley_side)
  -- 3. algebra
  have r51_1 : k ≠ 0 := by parley_side
  have r51_2 : k + 1 ≠ 0 := by parley_side
  have s3 : 1 / (k : ℚ) - 1 / ((k : ℚ) + 1) = 1 / ((k : ℚ) * ((k : ℚ) + 1)) := by parley_ring
  -- 4. join 2, 3
  have s4 : k * (k + 1) ≠ 0 ∧ 1 / (k : ℚ) - 1 / ((k : ℚ) + 1) = 1 / ((k : ℚ) * ((k : ℚ) + 1)) := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.AProductDivisorBelowALineSayingIt

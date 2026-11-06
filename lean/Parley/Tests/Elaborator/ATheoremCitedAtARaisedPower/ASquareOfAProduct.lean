module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-theorem-cited-at-a-raised-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.ASquareOfAProduct

theorem a_square_of_a_product (a : ℝ) (b : ℝ) :
    (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
  -- 1. mun:power-of-product n := 2
  have s1 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := a) (b := b) (n := (2 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := a) (b := b) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := a) (b := b) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := a) (b := b) (n := (2 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_power_of_product (a := a) (b := b) (n := (2 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := a) (b := b) (n := (2 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := a) (b := b) (n := (2 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := a) (b := b) (n := (2 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := a) (b := b) (n := (2 : ℤ)) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.ASquareOfAProduct

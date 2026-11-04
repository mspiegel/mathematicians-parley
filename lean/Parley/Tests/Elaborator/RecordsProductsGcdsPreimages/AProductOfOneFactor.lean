module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductOfOneFactor

theorem a_product_of_one_factor (t : ℤ → ℝ) :
    (∏ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (t k : ℝ)) = t 1 := by
  -- 1. mun:product-single a := 1
  have s1 : (∏ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (t k : ℝ)) = t 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_single (t := t) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := t) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := t) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_single (t := t) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_single (t := t) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := t) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := t) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := t) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := t) (a := (1 : ℤ))); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductOfOneFactor

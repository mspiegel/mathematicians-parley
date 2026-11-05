module

public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Tests.Notations.Sums.AProductScaled

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.AProductScaledCited

theorem a_product_scaled_cited (Y : Set ℤ) (hH1 : Y ⊆ (Set.univ : Set ℤ)) (hH2 : Y.Finite) :
    (∏ᶠ k ∈ Y, (k * 3 : ℤ)) = 3 ^ Y.ncard * (∏ᶠ k ∈ Y, (k : ℤ)) := by
  -- 1. thm:a-product-scaled X := Y, from H1, H2
  have s1 : (∏ᶠ k ∈ Y, (k * 3 : ℤ)) = 3 ^ Y.ncard * (∏ᶠ k ∈ Y, (k : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Tests.Notations.Sums.AProductScaled.a_product_scaled (X := Y) hH1 hH2) | (have h := (Parley.Tests.Notations.Sums.AProductScaled.a_product_scaled (X := Y) hH1 hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Notations.Sums.AProductScaled.a_product_scaled (X := Y) hH1 hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Notations.Sums.AProductScaled.a_product_scaled (X := Y) hH1 hH2) | exact_mod_cast ((Parley.Tests.Notations.Sums.AProductScaled.a_product_scaled (X := Y) hH1 hH2)).symm | (have h := (Parley.Tests.Notations.Sums.AProductScaled.a_product_scaled (X := Y) hH1 hH2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Notations.Sums.AProductScaled.a_product_scaled (X := Y) hH1 hH2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Notations.Sums.AProductScaled.a_product_scaled (X := Y) hH1 hH2); parley_int_power h) | (have h := (Parley.Tests.Notations.Sums.AProductScaled.a_product_scaled (X := Y) hH1 hH2); parley_set_side)
  all_goals exact s1

end Parley.Tests.Notations.Sums.AProductScaledCited

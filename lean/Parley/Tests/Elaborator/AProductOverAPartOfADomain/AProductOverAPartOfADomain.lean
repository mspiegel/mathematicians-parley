module

public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-product-over-a-part-of-a-domain.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AProductOverAPartOfADomain.AProductOverAPartOfADomain

theorem a_product_over_a_part_of_a_domain (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (L : Set ℤ) (hH2 : L ⊆ X) (hH3 : L.Finite) (f : ℤ → ℤ) (hH4 : Set.MapsTo f X (Set.univ : Set ℤ)) (hH5 : ∀ x ∈ L, True) (hH6 : ∀ x ∈ L, True) :
    (∏ᶠ x ∈ L, (x * f x : ℤ)) = (∏ᶠ x ∈ L, (x : ℤ)) * (∏ᶠ x ∈ L, (f x : ℤ)) := by
  -- 1. mun:product-of-products, from H3, H5, H6
  have s1 : (∏ᶠ x ∈ L, (x * f x : ℤ)) = (∏ᶠ x ∈ L, (x : ℤ)) * (∏ᶠ x ∈ L, (f x : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := f) (X := L) hH3) | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := f) (X := L) hH3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := f) (X := L) hH3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := f) (X := L) hH3) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := f) (X := L) hH3)).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := f) (X := L) hH3); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := f) (X := L) hH3); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := f) (X := L) hH3); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := f) (X := L) hH3); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.AProductOverAPartOfADomain.AProductOverAPartOfADomain

module

public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from corpus/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Sums.ProductFactor

theorem product_factor (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (hH2 : X.Finite) (c : ℤ) :
    (∏ᶠ x ∈ X, (x * c : ℤ)) = c ^ X.ncard * (∏ᶠ x ∈ X, (x : ℤ)) := by
  -- 1. proof
  have s1 : ∀ x ∈ X, True := by
    intro x hK1
    -- 1.1. mun:in-subset, from H1, K1
    -- 1.2. membership, from 1.1
    all_goals parley_set_side
  -- 2. mun:product-of-products, from H2, 1
  have s2 : (∏ᶠ x ∈ X, (x * c : ℤ)) = (∏ᶠ x ∈ X, (x : ℤ)) * (∏ᶠ x ∈ X, (c : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := (fun x : ℤ => c)) (X := X) hH2) | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := (fun x : ℤ => c)) (X := X) hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := (fun x : ℤ => c)) (X := X) hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := (fun x : ℤ => c)) (X := X) hH2) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := (fun x : ℤ => c)) (X := X) hH2)).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := (fun x : ℤ => c)) (X := X) hH2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := (fun x : ℤ => c)) (X := X) hH2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := (fun x : ℤ => c)) (X := X) hH2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := (fun x : ℤ => c)) (X := X) hH2); parley_set_side)
  -- 3. substitute
  have s3 : (∏ᶠ x ∈ X, (x * c : ℤ)) = (∏ᶠ x ∈ X, (x : ℤ)) * c ^ X.ncard := by
    have c1 : (∏ᶠ x ∈ X, (c : ℤ)) = c ^ X.ncard := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_constant (X := X) hH2 (c := c)) | (have h := (Parley.Items.Stdlib.Sums.mun_product_constant (X := X) hH2 (c := c)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_constant (X := X) hH2 (c := c)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_constant (X := X) hH2 (c := c))) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_constant (X := X) hH2 (c := c)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_constant (X := X) hH2 (c := c))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_constant (X := X) hH2 (c := c)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_constant (X := X) hH2 (c := c)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_constant (X := X) hH2 (c := c)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_constant (X := X) hH2 (c := c)); parley_set_side)
    have row1 : (∏ᶠ x ∈ X, (x * c : ℤ)) = (∏ᶠ x ∈ X, (x : ℤ)) * c ^ X.ncard := by parley_subst_at c1 s2
    exact row1
  -- 4. mun:product-integer, from H1, H2
  -- 5. mun:card-nat0, from H2
  have s5 : 0 ≤ (X.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2); parley_set_side)
  -- 6. algebra, from 3
  have s6 : (∏ᶠ x ∈ X, (x * c : ℤ)) = c ^ X.ncard * (∏ᶠ x ∈ X, (x : ℤ)) := by linear_combination (norm := parley_norm) s3
  all_goals exact s6

end Parley.Stdlib.Sums.ProductFactor

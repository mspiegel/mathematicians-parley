module

public import NormTactics
public import PowerTactics
public import SetTactics
public import Sets
public import SubstTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.ProductCoprime

set_option maxHeartbeats 400000 in
theorem product_coprime (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (hH2 : X.Finite) (n : ℤ) (hH3 : 0 < n) (hH4 : ∀ y ∈ X, (Int.gcd y n : ℤ) = 1) :
    (Int.gcd (∏ᶠ x ∈ X, (x : ℤ)) n : ℤ) = 1 := by
  -- 1. proof
  have s1 : ∀ x ∈ X, True := by
    intro x hK1
    -- 1.1. mun:in-subset, from H1, K1
    -- 1.2. membership, from 1.1
    exact trivial
  -- 2. induction on Y starting at ∅
  have r617_1 : X.Finite := by parley_set_side
  have s2 : ∀ Y ∈ 𝒫 X, (Int.gcd (∏ᶠ x ∈ Y, (x : ℤ)) n : ℤ) = 1 := by
    refine LeanBridges.Sets.subset_induction (by parley_finite) ?_ ?_
    · skip
      -- 2.1. mun:gcd-one a := n
      have s2_1 : (Int.gcd n (1 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := n))
      -- 2.2. mun:gcd-commutes a := 1, b := n
      have s2_2 : (Int.gcd (1 : ℤ) n : ℤ) = (Int.gcd n (1 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (1 : ℤ)) (b := n))
      -- 2.3. transitivity, from 2.2, 2.1
      have s2_3 : (Int.gcd (1 : ℤ) n : ℤ) = 1 := by parley_set_side
      -- 2.4. substitute
      have c1 : 1 = (∏ᶠ x ∈ (∅ : Set ℤ), (x : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_empty (X := Set.univ) (t := (fun x : ℤ => x))) | (have h := (Parley.Items.Stdlib.Sums.mun_product_empty (X := Set.univ) (t := (fun x : ℤ => x))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_empty (X := Set.univ) (t := (fun x : ℤ => x))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_empty (X := Set.univ) (t := (fun x : ℤ => x))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_empty (X := Set.univ) (t := (fun x : ℤ => x)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_empty (X := Set.univ) (t := (fun x : ℤ => x))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_empty (X := Set.univ) (t := (fun x : ℤ => x))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_empty (X := Set.univ) (t := (fun x : ℤ => x))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_empty (X := Set.univ) (t := (fun x : ℤ => x))); parley_set_side)
      have row1 : (Int.gcd (∏ᶠ x ∈ (∅ : Set ℤ), (x : ℤ)) n : ℤ) = 1 := by parley_subst_at c1 s2_3
      exact row1
    · intro Y hK hIH
      intro a hK2
      -- 2.5. def:difference u := a, Y := X, Z := Y, from K2
      have s2_5 : a ∈ X ∧ ¬ a ∈ Y := ((Parley.Items.Stdlib.Sets.def_difference (Y := X) (Z := Y) (u := a))).mp hK2
      -- 2.6. mun:finite-part, from H2, K
      have s2_6 : Y.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := Y) hH2 hK)
      -- 2.7. instantiate y := a in H4, from 2.5
      have s2_7 : (Int.gcd a n : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (hH4 a (by parley_set_side)) | (have h := (hH4 a (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH4 a (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH4 a (by parley_set_side)) | exact_mod_cast ((hH4 a (by parley_set_side))).symm | (have h := (hH4 a (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH4 a (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH4 a (by parley_set_side)); parley_int_power h) | (have h := (hH4 a (by parley_set_side)); parley_set_side)
      -- 2.8. mun:subset-transitive X := Y, Y := X, Z := ℤ, from H1, K
      have s2_8 : Y ⊆ (Set.univ : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := Y) (Y := X) (Z := (Set.univ : Set ℤ)) hK (by parley_whole_side))
      -- 2.9. mun:product-integer X := Y, from 2.6, 2.8
      -- 2.10. mun:in-subset, from H1, 2.5
      -- 2.11. mun:coprime-product x := ∏(x ∈ Y) x, y := a, from IH, 2.7, 2.9, 2.10
      have s2_11 : (Int.gcd ((∏ᶠ x ∈ Y, (x : ℤ)) * a) n : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_product (x := ∏ᶠ x ∈ Y, (x : ℤ)) (y := a) (n := n) (by parley_set_side) hIH s2_7)
      -- 2.12. substitute
      have c1 : (∏ᶠ x ∈ Y, (x : ℤ)) * a = (∏ᶠ x ∈ (Y ∪ ({a} : Set ℤ)), (x : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_add_one (t := (fun x : ℤ => x)) (X := X) (Y := Y) (a := a) (by parley_set_side) s2_6 s2_5.1 s2_5.2) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := (fun x : ℤ => x)) (X := X) (Y := Y) (a := a) (by parley_set_side) s2_6 s2_5.1 s2_5.2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := (fun x : ℤ => x)) (X := X) (Y := Y) (a := a) (by parley_set_side) s2_6 s2_5.1 s2_5.2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_add_one (t := (fun x : ℤ => x)) (X := X) (Y := Y) (a := a) (by parley_set_side) s2_6 s2_5.1 s2_5.2) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_add_one (t := (fun x : ℤ => x)) (X := X) (Y := Y) (a := a) (by parley_set_side) s2_6 s2_5.1 s2_5.2)).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := (fun x : ℤ => x)) (X := X) (Y := Y) (a := a) (by parley_set_side) s2_6 s2_5.1 s2_5.2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := (fun x : ℤ => x)) (X := X) (Y := Y) (a := a) (by parley_set_side) s2_6 s2_5.1 s2_5.2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := (fun x : ℤ => x)) (X := X) (Y := Y) (a := a) (by parley_set_side) s2_6 s2_5.1 s2_5.2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := (fun x : ℤ => x)) (X := X) (Y := Y) (a := a) (by parley_set_side) s2_6 s2_5.1 s2_5.2); parley_set_side)
      have row1 : (Int.gcd (∏ᶠ x ∈ (Y ∪ ({a} : Set ℤ)), (x : ℤ)) n : ℤ) = 1 := by parley_subst_at c1 s2_11
      exact row1
  -- 3. instantiate Y := X in line 2
  have r668_1 : X ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := X))
  first | linear_combination (norm := parley_norm) (s2 X (by parley_set_side)) | (have h := (s2 X (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s2 X (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s2 X (by parley_set_side)) | exact_mod_cast ((s2 X (by parley_set_side))).symm | (have h := (s2 X (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s2 X (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s2 X (by parley_set_side)); parley_int_power h) | (have h := (s2 X (by parley_set_side)); parley_set_side)

end Parley.Stdlib.Divisibility.ProductCoprime

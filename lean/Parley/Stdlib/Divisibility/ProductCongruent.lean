module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Sets

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.ProductCongruent

theorem product_congruent (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (hH2 : X.Finite) (c : ℤ) (n : ℤ) (hH4 : 0 < n) (f : ℤ → ℤ) (hH5 : Set.MapsTo f X X) (hH6 : ∀ y ∈ X, y * c ≡ f y [ZMOD n]) :
    (∏ᶠ x ∈ X, (x * c : ℤ)) ≡ (∏ᶠ x ∈ X, (f x : ℤ)) [ZMOD n] := by
  -- 1. proof
  have s1 : ∀ x ∈ X, True := by
    intro x hK1
    -- 1.1. mun:in-subset, from H1, K1
    -- 1.2. membership, from 1.1
    all_goals parley_set_side
  -- 2. thm:product-congruent-termwise, from H2, H6, 1
  have s2 : (∏ᶠ x ∈ X, (x * c : ℤ)) ≡ (∏ᶠ x ∈ X, (f x : ℤ)) [ZMOD n] := by first | exact (Parley.Items.Stdlib.Divisibility.thm_product_congruent_termwise (t := (fun x : ℤ => x * c)) (u := f) (X := X) hH2 (n := n) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Divisibility.thm_product_congruent_termwise (t := (fun x : ℤ => x * c)) (u := f) (X := X) hH2 (n := n) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_product_congruent_termwise (t := (fun x : ℤ => x * c)) (u := f) (X := X) hH2 (n := n) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_product_congruent_termwise (t := (fun x : ℤ => x * c)) (u := f) (X := X) hH2 (n := n) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_product_congruent_termwise (t := (fun x : ℤ => x * c)) (u := f) (X := X) hH2 (n := n) (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals exact s2

end Parley.Stdlib.Divisibility.ProductCongruent

module

public import AlgebraTactics
public import NormTactics
public import PowerTactics
public import SetTactics
public import Sets
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.ProductCongruentTermwise

set_option maxHeartbeats 600000 in
theorem product_congruent_termwise {α : Type*} (X : Set α) (hH2 : X.Finite) (n : ℤ) (hH3 : 0 < n) (t : α → ℤ) (hH4 : Set.MapsTo t X (Set.univ : Set ℤ)) (u : α → ℤ) (hH5 : Set.MapsTo u X (Set.univ : Set ℤ)) (hH6 : ∀ x ∈ X, t x ≡ u x [ZMOD n]) :
    (∏ᶠ x ∈ X, (t x : ℤ)) ≡ (∏ᶠ x ∈ X, (u x : ℤ)) [ZMOD n] := by
  -- 1. mun:product-integer-terms, from H2
  have s1 : ∀ Z ∈ 𝒫 X, True := (Parley.Items.Stdlib.Sums.mun_product_integer_terms (t := t) (X := X) hH2)
  -- 2. mun:product-integer-terms t := u, from H2
  have s2 : ∀ Z ∈ 𝒫 X, True := (Parley.Items.Stdlib.Sums.mun_product_integer_terms (t := u) (X := X) hH2)
  -- 3. induction on Y starting at ∅
  have r691_1 : X.Finite := by parley_set_side
  have s3 : ∀ Y ∈ 𝒫 X, (∏ᶠ x ∈ Y, (t x : ℤ)) ≡ (∏ᶠ x ∈ Y, (u x : ℤ)) [ZMOD n] := by
    refine LeanBridges.Sets.subset_induction (by parley_finite) ?_ ?_
    · skip
      -- 3.1. algebra
      have s3_1 : 1 - 1 = n * 0 := by parley_ring
      -- 3.2. def:divides d := n, n := 1 − 1, from 3.1
      have s3_2 : n ∣ (1 - 1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := n) (n := (1 - 1 : ℤ)))).mpr ⟨(0 : ℤ), s3_1⟩
      -- 3.3. def:congruent-mod a := 1, b := 1, from 3.2
      have s3_3 : (1 : ℤ) ≡ (1 : ℤ) [ZMOD n] := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := (1 : ℤ)) (b := (1 : ℤ)))).mpr s3_2
      -- 3.4. substitute
      have s3_4 : (∏ᶠ x ∈ (∅ : Set α), (t x : ℤ)) ≡ (1 : ℤ) [ZMOD n] := by
        have c1 : 1 = (∏ᶠ x ∈ (∅ : Set α), (t x : ℤ)) := (Parley.Items.Stdlib.Sums.mun_product_empty (X := X) (t := t)).symm
        have row1 : (∏ᶠ x ∈ (∅ : Set α), (t x : ℤ)) ≡ (1 : ℤ) [ZMOD n] := by parley_subst_at c1 s3_3
        exact row1
      -- 3.5. substitute
      have c1 : 1 = (∏ᶠ x ∈ (∅ : Set α), (u x : ℤ)) := (Parley.Items.Stdlib.Sums.mun_product_empty (X := X) (t := u)).symm
      have row1 : (∏ᶠ x ∈ (∅ : Set α), (t x : ℤ)) ≡ (∏ᶠ x ∈ (∅ : Set α), (u x : ℤ)) [ZMOD n] := by parley_subst_at c1 s3_4
      exact row1
    · intro Y hK hIH
      intro a hK2
      -- 3.6. def:difference u := a, Y := X, Z := Y, from K2
      have s3_6 : a ∈ X ∧ ¬ a ∈ Y := ((Parley.Items.Stdlib.Sets.def_difference (Y := X) (Z := Y) (u := a))).mp hK2
      -- 3.7. mun:finite-part, from H2, K
      have s3_7 : Y.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := Y) hH2 hK)
      -- 3.8. instantiate Z := Y in line 1, from K
      -- 3.9. instantiate Z := Y in line 2, from K
      -- 3.10. mun:function-value f := t, D := X, E := ℤ, x := a, from 3.6
      -- 3.11. mun:function-value f := u, D := X, E := ℤ, x := a, from 3.6
      -- 3.12. def:congruent-mod a := ∏(x ∈ Y) t(x), b := ∏(x ∈ Y) u(x), from IH, 3.8, 3.9
      have s3_12 : n ∣ (∏ᶠ x ∈ Y, (t x : ℤ)) - (∏ᶠ x ∈ Y, (u x : ℤ)) := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := ∏ᶠ x ∈ Y, (t x : ℤ)) (b := ∏ᶠ x ∈ Y, (u x : ℤ)))).mp hIH
      -- 3.13. instantiate x := a in H6, from 3.6
      have s3_13 : t a ≡ u a [ZMOD n] := by first | exact (hH6 a (by parley_set_side)) | exact ((hH6 a (by parley_set_side))).symm | simpa using (hH6 a (by parley_set_side)) | exact_mod_cast (hH6 a (by parley_set_side)) | (have h := (hH6 a (by parley_set_side)); parley_set_side)
      -- 3.14. def:congruent-mod a := t(a), b := u(a), from 3.10, 3.11, 3.13
      have s3_14 : n ∣ t a - u a := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := t a) (b := u a))).mp s3_13
      -- 3.15. mun:divides-combination e := n, a := ∏(x ∈ Y) t(x) − ∏(x ∈ Y) u(x), b := t(a) − u(a), x := t(a), y := ∏(x ∈ Y) u(x), from 3.8, 3.9, 3.10, 3.11, 3.12, 3.14
      have s3_15 : n ∣ ((∏ᶠ x ∈ Y, (t x : ℤ)) - (∏ᶠ x ∈ Y, (u x : ℤ))) * t a + (t a - u a) * (∏ᶠ x ∈ Y, (u x : ℤ)) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := (∏ᶠ x ∈ Y, (t x : ℤ)) - (∏ᶠ x ∈ Y, (u x : ℤ))) (b := t a - u a) (x := t a) (y := ∏ᶠ x ∈ Y, (u x : ℤ)) s3_12 s3_14)
      -- 3.16. substitute
      have s3_16 : n ∣ (∏ᶠ x ∈ Y, (t x : ℤ)) * t a - (∏ᶠ x ∈ Y, (u x : ℤ)) * u a := by
        have c1 : ((∏ᶠ x ∈ Y, (t x : ℤ)) - (∏ᶠ x ∈ Y, (u x : ℤ))) * t a + (t a - u a) * (∏ᶠ x ∈ Y, (u x : ℤ)) = (∏ᶠ x ∈ Y, (t x : ℤ)) * t a - (∏ᶠ x ∈ Y, (u x : ℤ)) * u a := by parley_ring
        have row1 : n ∣ (∏ᶠ x ∈ Y, (t x : ℤ)) * t a - (∏ᶠ x ∈ Y, (u x : ℤ)) * u a := by parley_subst_at c1 s3_15
        exact row1
      -- 3.17. def:congruent-mod a := (∏(x ∈ Y) t(x))·t(a), b := (∏(x ∈ Y) u(x))·u(a), from 3.8, 3.9, 3.10, 3.11, 3.16
      have s3_17 : (∏ᶠ x ∈ Y, (t x : ℤ)) * t a ≡ (∏ᶠ x ∈ Y, (u x : ℤ)) * u a [ZMOD n] := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := (∏ᶠ x ∈ Y, (t x : ℤ)) * t a) (b := (∏ᶠ x ∈ Y, (u x : ℤ)) * u a))).mpr s3_16
      -- 3.18. substitute
      have s3_18 : (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (t x : ℤ)) ≡ (∏ᶠ x ∈ Y, (u x : ℤ)) * u a [ZMOD n] := by
        have c1 : (∏ᶠ x ∈ Y, (t x : ℤ)) * t a = (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (t x : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_add_one (t := t) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := t) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := t) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_add_one (t := t) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_add_one (t := t) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2)).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := t) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := t) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := t) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := t) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); parley_set_side)
        have row1 : (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (t x : ℤ)) ≡ (∏ᶠ x ∈ Y, (u x : ℤ)) * u a [ZMOD n] := by parley_subst_at c1 s3_17
        exact row1
      -- 3.19. substitute
      have c1 : (∏ᶠ x ∈ Y, (u x : ℤ)) * u a = (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (u x : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_add_one (t := u) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := u) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := u) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_add_one (t := u) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_add_one (t := u) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2)).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := u) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := u) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := u) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := u) (X := X) (Y := Y) (a := a) (by parley_set_side) s3_7 s3_6.1 s3_6.2); parley_set_side)
      have row1 : (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (t x : ℤ)) ≡ (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (u x : ℤ)) [ZMOD n] := by parley_subst_at c1 s3_18
      exact row1
  -- 4. instantiate Y := X in line 3
  have r776_1 : X ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := X))
  first | exact (s3 X (by parley_set_side)) | exact ((s3 X (by parley_set_side))).symm | simpa using (s3 X (by parley_set_side)) | exact_mod_cast (s3 X (by parley_set_side)) | (have h := (s3 X (by parley_set_side)); parley_set_side)

end Parley.Stdlib.Divisibility.ProductCongruentTermwise

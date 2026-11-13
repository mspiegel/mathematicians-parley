module

public import InstanceTactics
public import NormTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from corpus/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Sums.ProductReorder

theorem product_reorder (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (hH2 : X.Finite) (f : ℤ → ℤ) (hH3 : Set.MapsTo f X X ∧ Set.InjOn f X) :
    (∏ᶠ x ∈ X, (f x : ℤ)) = (∏ᶠ x ∈ X, (x : ℤ)) := by
  -- 1. def:one-to-one Y := X, from H3
  have s1 : Set.MapsTo f X X ∧ (∀ s ∈ X, ∀ t ∈ X, f s = f t → s = t) := by exact ((Parley.Items.Stdlib.Functions.def_one_to_one (X := X) (Y := X) (f := f) hH3.1)).mp hH3
  -- 2. mun:subset-self
  have s2 : X ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := X))
  -- 3. proof
  have s3 : ∀ x ∈ X, f x ∈ f '' (X ∩ X) := by
    intro x hK1
    -- 3.1. mun:value-in-image W := X, Y := X, s := x, from 2
    exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := X) (Y := X) (f := f) (s := x) (W := Set.univ) s2 hK1 (Set.mapsTo_univ _ _))
  -- 4. mun:function-into E := f, Y := f[X], from 3
  have s4 : Set.MapsTo f X (f '' (X ∩ X)) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := X) (Y := f '' (X ∩ X)) s3)
  -- 5. proof
  have s5 : ∀ y ∈ f '' (X ∩ X), ∃ x ∈ X, y = f x := by
    intro y hK2
    -- 5.1. def:image u := y, W := X, Y := X, from K2, 2
    exact ((Parley.Items.Stdlib.Functions.def_image (X := X) (Y := X) (f := f) (u := y) (W := Set.univ) s2 (Set.mapsTo_univ _ _))).mp hK2
  -- 6. def:onto Y := f[X], from 4, 5
  have s6 : Set.MapsTo f X (f '' (X ∩ X)) ∧ Set.SurjOn f X (f '' (X ∩ X)) := ((Parley.Items.Stdlib.Functions.def_onto (X := X) (Y := f '' (X ∩ X)) (f := f) s4)).mpr ⟨s4, s5⟩
  -- 7. def:one-to-one Y := f[X], from 1, 4
  have s7 : Set.MapsTo f X (f '' (X ∩ X)) ∧ Set.InjOn f X := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := X) (Y := f '' (X ∩ X)) (f := f) s4)).mpr ⟨s4, s1.2⟩
  -- 8. def:one-to-one-onto Y := f[X], from 6, 7
  have s8 : Set.MapsTo f X (f '' (X ∩ X)) ∧ Set.InjOn f X ∧ Set.SurjOn f X (f '' (X ∩ X)) := ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := X) (Y := f '' (X ∩ X)) (f := f) s6.1)).mpr ⟨s7, s6⟩
  -- 9. def:bijection Y := f[X], from 8
  have s9 : ∃ g : ℤ → ℤ, Set.BijOn g X (f '' (X ∩ X)) := by exact (Parley.Items.Stdlib.Functions.def_bijection (X := X) (Y := f '' (X ∩ X)) (f := f) s8)
  -- 10. mun:card-equal Y := f[X], from H2, 9
  have s10 : ((X.ncard : ℕ) : ℕ∞) = (f '' (X ∩ X)).encard := by exact (Parley.Items.Stdlib.Counting.mun_card_equal (X := X) (Y := f '' (X ∩ X)) hH2 s9)
  -- 11. mun:image-within W := X, Y := X
  have s11 : f '' (X ∩ X) ⊆ X := by exact (Parley.Items.Stdlib.Functions.mun_image_within (X := X) (W := X) (Y := X) (f := f) hH3.1)
  -- 12. mun:card-difference Y := f[X], from H2, 11
  have s12 : ((X \ f '' (X ∩ X)).ncard : ℤ) = (X.ncard : ℤ) - ((f '' (X ∩ X)).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_difference (X := X) (Y := f '' (X ∩ X)) hH2 s11)
  -- 13. algebra, from 10, 12
  have r222_1 : 0 ≤ (X.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2)
  have s13 : ((X \ f '' (X ∩ X)).ncard : ℤ) = 0 := by parley_count_int; (linear_combination (norm := parley_norm) s10 + s12)
  -- 14. mun:card-zero X := X ∖ f[X], from 13
  have s14 : X \ f '' (X ∩ X) = ∅ := by exact (Parley.Items.Stdlib.Counting.mun_card_zero (X := X \ f '' (X ∩ X)) (by (have h := s13; rw [← Set.Finite.cast_ncard_eq (((hH2).subset (fun _ h => h.1) : (X \ f '' (X ∩ X) : Set ℤ).Finite))]; norm_cast at h ⊢; all_goals omega)))
  -- 15. mun:nothing-left-outside Y := X, X := f[X], from 14
  have s15 : X ⊆ f '' (X ∩ X) := ((Parley.Items.Stdlib.Sets.mun_nothing_left_outside (X := f '' (X ∩ X)) (Y := X))).mpr s14
  -- 16. proof
  have s16 : ∀ y ∈ X, ∃ x ∈ X, y = f x := by
    intro y hK3
    -- 16.1. mun:in-subset, from K3, 15
    have s16_1 : y ∈ f '' (X ∩ X) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := f '' (X ∩ X)) (u := y) s15 hK3)
    -- 16.2. def:image u := y, W := X, Y := X, from 2, 16.1
    exact ((Parley.Items.Stdlib.Functions.def_image (X := X) (Y := X) (f := f) (u := y) (W := Set.univ) s2 (Set.mapsTo_univ _ _))).mp s16_1
  -- 17. def:onto Y := X, from 1, 16
  have s17 : Set.MapsTo f X X ∧ Set.SurjOn f X X := ((Parley.Items.Stdlib.Functions.def_onto (X := X) (Y := X) (f := f) s1.1)).mpr ⟨s1.1, s16⟩
  -- 18. def:one-to-one-onto Y := X, from H3, 17
  have s18 : Set.MapsTo f X X ∧ Set.InjOn f X ∧ Set.SurjOn f X X := ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := X) (Y := X) (f := f) hH3.1)).mpr ⟨hH3, s17⟩
  -- 19. proof
  have s19 : ∀ z ∈ X, True := by
    intro z hK4
    -- 19.1. mun:in-subset, from H1, K4
    -- 19.2. membership, from 19.1
    exact trivial
  -- 20. mun:product-reindex Y := X, Z := X, g := f, from H2, 18, 19
  have s20 : (∏ᶠ z ∈ X, (z : ℤ)) = (∏ᶠ y ∈ X, (f y : ℤ)) := by
    have hI : (∏ᶠ a ∈ X, (a : ℤ)) = (∏ᶠ y ∈ X, (f y : ℤ)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_product_reindex (t := (fun z : ℤ => z)) (Y := X) (Z := X) (g := f) hH2 s18))
    exact hI
  -- 21. restate 20
  exact s20.symm

end Parley.Stdlib.Sums.ProductReorder

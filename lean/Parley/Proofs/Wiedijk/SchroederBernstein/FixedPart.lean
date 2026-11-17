module

public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/schroeder-bernstein.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.SchroederBernstein.FixedPart

theorem fixed_part {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (B : Set β) (f : α → β) (hH3 : Set.MapsTo f A B) (g : β → α) (hH4 : Set.MapsTo g B A) :
    (∃ C ∈ 𝒫 A, g '' (B ∩ (B \ f '' (A ∩ C))) = A \ C) := by
  set M : Set α → Set α := fun X : Set α => g '' (B ∩ (B \ f '' (A ∩ X))) with hD1
  set D : Set (Set α) := {X ∈ 𝒫 A | M X ∩ X = ∅} with hD2
  set C : Set α := ⋃ X ∈ D, X with hD3
  -- 1. mun:image-within f := g, from D1
  have s1 : ∀ X ∈ 𝒫 A, M X ⊆ A := by
    intro X h_X
    simp only [hD1] at ⊢
    push_cast at ⊢
    exact (Parley.Items.Stdlib.Functions.mun_image_within (X := B) (W := A) (Y := B \ f '' (A ∩ X)) (f := g) hH4)
  -- 2. proof
  have s2 : ∀ X ∈ 𝒫 A, ∀ Y ∈ 𝒫 A, X ⊆ Y → M Y ⊆ M X := by
    intro X hK3
    intro Y hK4
    intro hA1
    -- 2.1. mun:image-monotone, from A1
    have s2_1 : f '' (A ∩ X) ⊆ f '' (A ∩ Y) := by exact (Parley.Items.Stdlib.Functions.mun_image_monotone (X := A) (Y := X) (Z := Y) (f := f) (W := B) hA1 hH3)
    -- 2.2. mun:difference-reverses, from 2.1
    have s2_2 : B \ f '' (A ∩ Y) ⊆ B \ f '' (A ∩ X) := by exact (Parley.Items.Stdlib.Sets.mun_difference_reverses (X := f '' (A ∩ X)) (Y := f '' (A ∩ Y)) (Z := B) s2_1)
    -- 2.3. mun:image-monotone f := g, from D1, 2.2
    have r62_1 : X ⊆ A := by exact hK3
    have r62_2 : Y ⊆ A := by exact hK4
    simp only [hD1] at ⊢
    push_cast at ⊢
    exact (Parley.Items.Stdlib.Functions.mun_image_monotone (X := B) (Y := B \ f '' (A ∩ Y)) (Z := B \ f '' (A ∩ X)) (f := g) (W := A) s2_2 hH4)
  -- 3. def:part-builder, from D2
  have s3 : ∀ X ∈ D, X ⊆ A := by intro X h_X; (exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun X : Set α => M X ∩ X = ∅)) (X := A) (u := X))).mp h_X).1)
  -- 4. mun:union-within, from D3, 3
  have s4 : C ⊆ A := by
    simp only [hD3] at ⊢
    push_cast at ⊢
    exact (Parley.Items.Stdlib.Sets.mun_union_within (D := D) (Z := A) s3)
  -- 5. instantiate X := C in line 1, from 4
  have s5 : M C ⊆ A := by exact (s1 C s4)
  -- 6. proof
  have s6 : ∀ X ∈ D, M C ∩ X = ∅ := by
    intro X hK6
    -- 6.1. def:part-builder, from D2, K6
    have s6_1 : X ⊆ A := by exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun X : Set α => M X ∩ X = ∅)) (X := A) (u := X))).mp hK6).1
    -- 6.2. def:part-builder, from D2, K6
    have s6_2 : M X ∩ X = ∅ := by exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun X : Set α => M X ∩ X = ∅)) (X := A) (u := X))).mp hK6).2
    -- 6.3. mun:union-contains-member Y := X, from D3, K6
    have s6_3 : X ⊆ C := by
      simp only [hD3] at ⊢
      push_cast at ⊢
      exact (Parley.Items.Stdlib.Sets.mun_union_contains_member (D := D) (Y := X) hK6)
    -- 6.4. instantiate X := X, Y := C in line 2, from 4, 6.1, 6.3
    have s6_4 : M C ⊆ M X := by exact (s2 X s6_1 C s4 s6_3)
    -- 6.5. mun:disjoint-within, from 6.2, 6.4
    exact (Parley.Items.Stdlib.Sets.mun_disjoint_within (X := M C) (Y := M X) (Z := X) s6_4 s6_2)
  -- 7. proof
  have s7 : ∀ a ∈ M C, a ∈ A \ C := by
    intro a hK7
    -- 7.1. mun:in-subset, from K7, 5
    have s7_1 : a ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := M C) (Y := A) (u := a) s5 hK7)
    -- 7.2. contradiction
    have s7_2 : ¬ a ∈ C := by
      intro hS1
      -- 7.2.1. obtain X: def:indexed-union u := a, from D3, S1
      obtain ⟨X, s7_2_1a, s7_2_1b⟩ := ((Parley.Items.Stdlib.Sets.def_indexed_union (D := D) (u := a))).mp hS1
      -- 7.2.2. instantiate X := X in line 6, from 7.2.1
      have s7_2_2 : M C ∩ X = ∅ := by exact (s6 X s7_2_1a)
      -- 7.2.3. mun:disjoint-member, from K7, 7.2.2
      have s7_2_3 : ¬ a ∈ X := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := M C) (Z := X) (u := a) s7_2_2 hK7)
      exact s7_2_3 s7_2_1b
    -- 7.3. def:difference, from 7.1, 7.2
    exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := a))).mpr ⟨s7_1, s7_2⟩
  -- 8. def:subset, from 7
  have s8 : M C ⊆ A \ C := ((Parley.Items.Stdlib.Sets.def_subset (X := M C) (Y := A \ C))).mpr s7
  -- 9. mun:complement-swap, from 4, 5, 8
  have s9 : C ⊆ A \ M C := by exact ((Parley.Items.Stdlib.Sets.mun_complement_swap (X := M C) (Y := C) (Z := A) s5 s4)).mp s8
  -- 10. mun:difference-subset
  have s10 : A \ M C ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := M C))
  -- 11. instantiate X := C, Y := A ∖ M(C) in line 2, from 4, 9, 10
  have s11 : M (A \ M C) ⊆ M C := by exact (s2 C s4 (A \ M C) s10 s9)
  -- 12. mun:disjoint-difference
  have s12 : M C ∩ (A \ M C) = ∅ := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_difference (Y := M C) (Z := A))
  -- 13. mun:disjoint-within, from 11, 12
  have s13 : M (A \ M C) ∩ (A \ M C) = ∅ := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_within (X := M (A \ M C)) (Y := M C) (Z := A \ M C) s11 s12)
  -- 14. def:part-builder u := A ∖ M(C), from D2, 10, 13
  have s14 : A \ M C ∈ D := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun X : Set α => M X ∩ X = ∅)) (X := A) (u := A \ M C))).mpr ⟨s10, s13⟩
  -- 15. mun:union-contains-member Y := A ∖ M(C), from D3, 14
  have s15 : A \ M C ⊆ C := by
    simp only [hD3] at ⊢
    push_cast at ⊢
    exact (Parley.Items.Stdlib.Sets.mun_union_contains_member (D := D) (Y := A \ M (⋃ X ∈ D, X)) s14)
  -- 16. mun:complement-swap-outside, from 15
  have s16 : A \ C ⊆ M C := by exact ((Parley.Items.Stdlib.Sets.mun_complement_swap_outside (X := C) (Y := M C) (Z := A))).mp s15
  -- 17. mun:subset-antisymmetric, from 8, 16
  have s17 : M C = A \ C := by exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := M C) (Y := A \ C) s8 s16)
  -- 18. exhibit, from D1, 4, 17
  exact ⟨C, s4, s17⟩

end Parley.Proofs.Wiedijk.SchroederBernstein.FixedPart

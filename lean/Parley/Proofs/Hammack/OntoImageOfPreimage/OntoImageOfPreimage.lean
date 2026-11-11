module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/onto-image-of-preimage.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OntoImageOfPreimage.OntoImageOfPreimage

theorem onto_image_of_preimage {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) :
    (Set.MapsTo f A B ∧ Set.SurjOn f A B ↔ (∀ Y ∈ 𝒫 B, f '' (A ∩ (A ∩ f ⁻¹' Y)) = Y)) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. def:onto, from D1
    have s1 : ∀ y ∈ B, ∃ x ∈ A, y = f x := by exact (((Parley.Items.Stdlib.Functions.def_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mp hD1).2
    -- 2. proof
    intro Y hK1
    -- 2.1. proof
    have s2_1 : ∀ u ∈ A ∩ f ⁻¹' Y, u ∈ A := by
      intro u hK2
      -- 2.1.1. def:preimage Z := Y, from K2
      exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp hK2).1
    -- 2.2. def:subset, from 2.1
    have s2_2 : A ∩ f ⁻¹' Y ⊆ A := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' Y) (Y := A))).mpr s2_1
    -- 2.3. proof
    have s2_3 : ∀ y ∈ f '' (A ∩ (A ∩ f ⁻¹' Y)), y ∈ Y := by
      intro y hK3
      -- 2.3.1. obtain s: def:image u := y, Y := f⁻¹[Y], from K3, 2.2
      obtain ⟨s, s2_3_1a, s2_3_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := A ∩ f ⁻¹' Y) (f := f) (u := y) (W := Set.univ) s2_2 (by parley_set_side))).mp hK3
      -- 2.3.2. def:preimage u := s, Z := Y, from 2.3.1
      have s2_3_2a : s ∈ A := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp s2_3_1a).1
      have s2_3_2b : f s ∈ Y := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp s2_3_1a).2
      -- 2.3.3. substitute y = f(s) (line 2.3.1) into line 2.3.2
      parley_subst_at s2_3_1b s2_3_2b
    -- 2.4. def:subset, from 2.3
    have s2_4 : f '' (A ∩ (A ∩ f ⁻¹' Y)) ⊆ Y := ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (A ∩ (A ∩ f ⁻¹' Y))) (Y := Y))).mpr s2_3
    -- 2.5. proof
    have s2_5 : ∀ y ∈ Y, y ∈ f '' (A ∩ (A ∩ f ⁻¹' Y)) := by
      intro y hK4
      -- 2.5.1. mun:in-subset X := Y, Y := B, u := y, from K1, K4
      have s2_5_1 : y ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := Y) (Y := B) (u := y) hK1 hK4)
      -- 2.5.2. instantiate y := y in line 1, from 2.5.1
      have s2_5_2 : ∃ x ∈ A, y = f x := by exact (s1 y s2_5_1)
      -- 2.5.3. obtain x from line 2.5.2
      obtain ⟨x, s2_5_3a, s2_5_3b⟩ := s2_5_2
      -- 2.5.4. substitute y = f(x) (line 2.5.3) into K4
      have s2_5_4 : f x ∈ Y := by parley_subst_at s2_5_3b hK4
      -- 2.5.5. def:preimage u := x, Z := Y, from 2.5.3, 2.5.4
      have s2_5_5 : x ∈ A ∩ f ⁻¹' Y := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := x) (W := Set.univ) (by parley_set_side))).mpr ⟨s2_5_3a, by parley_set_side⟩
      -- 2.5.6. mun:value-in-image Y := f⁻¹[Y], s := x, from 2.2, 2.5.5
      have s2_5_6 : f x ∈ f '' (A ∩ (A ∩ f ⁻¹' Y)) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A ∩ f ⁻¹' Y) (f := f) (s := x) (W := Set.univ) s2_2 s2_5_5 (by parley_set_side))
      -- 2.5.7. substitute y = f(x) (line 2.5.3) into line 2.5.6
      parley_subst_at s2_5_3b s2_5_6
    -- 2.6. def:subset, from 2.5
    have s2_6 : Y ⊆ f '' (A ∩ (A ∩ f ⁻¹' Y)) := ((Parley.Items.Stdlib.Sets.def_subset (X := Y) (Y := f '' (A ∩ (A ∩ f ⁻¹' Y))))).mpr s2_5
    -- 2.7. mun:subset-antisymmetric, from 2.4, 2.6
    exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (A ∩ (A ∩ f ⁻¹' Y))) (Y := Y) s2_4 s2_6)
  · skip
    intro hD2
    -- 3. proof
    have s3 : ∀ y ∈ B, ∃ x ∈ A, y = f x := by
      intro y hK5
      -- 3.1. mun:singleton-subset a := y, X := B, from K5
      have s3_1 : ({y} : Set α) ⊆ B := by exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := B) (a := y) hK5)
      -- 3.2. def:singleton x := y, a := y
      have s3_2 : y ∈ ({y} : Set α) := ((Parley.Items.Stdlib.Sets.def_singleton (a := y) (x := y))).mpr (by parley_set_side)
      -- 3.3. substitute
      have s3_3 : y ∈ f '' (A ∩ (A ∩ f ⁻¹' ({y} : Set α))) := by
        have c1 : ({y} : Set α) = f '' (A ∩ (A ∩ f ⁻¹' ({y} : Set α))) := by exact (hD2 ({y} : Set α) s3_1).symm
        have row1 : y ∈ f '' (A ∩ (A ∩ f ⁻¹' ({y} : Set α))) := by parley_subst_at c1 s3_2
        exact row1
      -- 3.4. proof
      have s3_4 : ∀ u ∈ A ∩ f ⁻¹' ({y} : Set α), u ∈ A := by
        intro u hK6
        -- 3.4.1. def:preimage Z := {y}, from K6
        exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := ({y} : Set α)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp hK6).1
      -- 3.5. def:subset, from 3.4
      have s3_5 : A ∩ f ⁻¹' ({y} : Set α) ⊆ A := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' ({y} : Set α)) (Y := A))).mpr s3_4
      -- 3.6. obtain s: def:image u := y, Y := f⁻¹[{y}], from 3.3, 3.5
      obtain ⟨s, s3_6a, s3_6b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := A ∩ f ⁻¹' ({y} : Set α)) (f := f) (u := y) (W := Set.univ) s3_5 (by parley_set_side))).mp s3_3
      -- 3.7. def:preimage u := s, Z := {y}, from 3.6
      have s3_7 : s ∈ A := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := ({y} : Set α)) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp s3_6a).1
      -- 3.8. exhibit, from 3.6, 3.7
      exact ⟨s, s3_7, s3_6b⟩
    -- 4. def:onto, from H3, 3
    exact ((Parley.Items.Stdlib.Functions.def_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mpr ⟨hH3, s3⟩

end Parley.Proofs.Hammack.OntoImageOfPreimage.OntoImageOfPreimage

module

public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage

/-! Written from proofs/hammack/one-to-one-preimage-of-image.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OneToOnePreimageOfImage.OneToOnePreimageOfImage

set_option maxHeartbeats 600000 in
theorem one_to_one_preimage_of_image {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) :
    (Set.MapsTo f A B ∧ Set.InjOn f A ↔ (∀ X ∈ 𝒫 A, A ∩ f ⁻¹' (f '' (A ∩ X)) = X)) := by
  -- the theorem. both directions
  have sThm : Set.MapsTo f A B ∧ Set.InjOn f A ↔ (∀ X ∈ 𝒫 A, A ∩ f ⁻¹' (f '' (A ∩ X)) = X) := by
    constructor
    · skip
      intro hD1
      -- 1. def:one-to-one, from D1
      have s1 : ∀ s ∈ A, ∀ t ∈ A, f s = f t → s = t := by first | exact (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side)).2; parley_set_side)
      -- 2. proof
      have s2 : ∀ X ∈ 𝒫 A, A ∩ f ⁻¹' (f '' (A ∩ X)) = X := by
        intro X hK1
        -- 2.1. proof
        have s2_1 : ∀ u ∈ A ∩ f ⁻¹' (f '' (A ∩ X)), u ∈ X := by
          intro u hK2
          -- 2.1.1. def:preimage Z := f[X], from K2
          have s2_1_1a : u ∈ A := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1; parley_set_side)
          have s2_1_1b : f u ∈ f '' (A ∩ X) := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2; parley_set_side)
          -- 2.1.2. obtain s: def:image u := f(u), Y := X, from K1, 2.1.1
          obtain ⟨s, s2_1_2a, s2_1_2b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := X) (f := f) (u := f u) (W := Set.univ) hK1 (by parley_set_side))).mp (by parley_set_side)
          -- 2.1.3. mun:in-subset Y := A, u := s, from K1, 2.1.2
          have s2_1_3 : s ∈ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) hK1 s2_1_2a) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) hK1 s2_1_2a)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) hK1 s2_1_2a) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) hK1 s2_1_2a) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) hK1 s2_1_2a); parley_set_side)
          -- 2.1.4. instantiate s := u, t := s in line 1, from 2.1.1, 2.1.2, 2.1.3
          have s2_1_4 : u = s := by first | exact (s1 u (by parley_set_side) s (by parley_set_side) (by parley_set_side)) | exact ((s1 u (by parley_set_side) s (by parley_set_side) (by parley_set_side))).symm | simpa using (s1 u (by parley_set_side) s (by parley_set_side) (by parley_set_side)) | exact_mod_cast (s1 u (by parley_set_side) s (by parley_set_side) (by parley_set_side)) | (have h := (s1 u (by parley_set_side) s (by parley_set_side) (by parley_set_side)); parley_set_side)
          -- 2.1.5. substitute u = s (line 2.1.4) into line 2.1.2
          have s2_1_5 : u ∈ X := by parley_subst_at s2_1_4 s2_1_2a
          all_goals exact s2_1_5
        -- 2.2. def:subset, from 2.1
        have s2_2 : A ∩ f ⁻¹' (f '' (A ∩ X)) ⊆ X := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' (f '' (A ∩ X))) (Y := X))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' (f '' (A ∩ X))) (Y := X))).mpr (by parley_set_side); parley_set_side)
        -- 2.3. thm:subset-of-preimage-of-image, from K1
        have s2_3 : X ⊆ A ∩ f ⁻¹' (f '' (A ∩ X)) := by first | exact (Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage.subset_of_preimage_of_image (A := A) (B := Set.univ) (f := f) (by parley_set_side) (X := X) hK1) | exact ((Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage.subset_of_preimage_of_image (A := A) (B := Set.univ) (f := f) (by parley_set_side) (X := X) hK1)).symm | simpa using (Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage.subset_of_preimage_of_image (A := A) (B := Set.univ) (f := f) (by parley_set_side) (X := X) hK1) | exact_mod_cast (Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage.subset_of_preimage_of_image (A := A) (B := Set.univ) (f := f) (by parley_set_side) (X := X) hK1) | (have h := (Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage.subset_of_preimage_of_image (A := A) (B := Set.univ) (f := f) (by parley_set_side) (X := X) hK1); parley_set_side)
        -- 2.4. mun:subset-antisymmetric, from 2.2, 2.3
        have s2_4 : A ∩ f ⁻¹' (f '' (A ∩ X)) = X := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (f '' (A ∩ X))) (Y := X) s2_2 s2_3) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (f '' (A ∩ X))) (Y := X) s2_2 s2_3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (f '' (A ∩ X))) (Y := X) s2_2 s2_3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (f '' (A ∩ X))) (Y := X) s2_2 s2_3) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (f '' (A ∩ X))) (Y := X) s2_2 s2_3); parley_set_side)
        all_goals exact s2_4
      all_goals parley_set_side
    · skip
      intro hD2
      -- 3. proof
      have s3 : ∀ s ∈ A, ∀ t ∈ A, f s = f t → s = t := by
        intro s hK3
        intro t hK4
        intro hA1
        -- 3.1. mun:singleton-subset a := t, X := A, from K4
        have s3_1 : ({t} : Set α) ⊆ A := by first | exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := A) (a := t) hK4) | exact ((Parley.Items.Stdlib.Sets.mun_singleton_subset (X := A) (a := t) hK4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := A) (a := t) hK4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := A) (a := t) hK4) | (have h := (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := A) (a := t) hK4); parley_set_side)
        -- 3.2. def:singleton x := t, a := t
        have s3_2 : t ∈ ({t} : Set α) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_singleton (a := t) (x := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_singleton (a := t) (x := t))).mpr (by parley_set_side); parley_set_side)
        -- 3.3. mun:value-in-image Y := {t}, s := t, from 3.1, 3.2
        have s3_3 : f t ∈ f '' (A ∩ ({t} : Set α)) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({t} : Set α)) (f := f) (s := t) (W := Set.univ) s3_1 s3_2 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({t} : Set α)) (f := f) (s := t) (W := Set.univ) s3_1 s3_2 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({t} : Set α)) (f := f) (s := t) (W := Set.univ) s3_1 s3_2 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({t} : Set α)) (f := f) (s := t) (W := Set.univ) s3_1 s3_2 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({t} : Set α)) (f := f) (s := t) (W := Set.univ) s3_1 s3_2 (by parley_set_side)); parley_set_side)
        -- 3.4. substitute f(s) = f(t) (A1) into line 3.3
        have s3_4 : f s ∈ f '' (A ∩ ({t} : Set α)) := by parley_subst_at hA1 s3_3
        -- 3.5. def:preimage Z := f[{t}], from K3, 3.4
        have s3_5 : s ∈ A ∩ f ⁻¹' (f '' (A ∩ ({t} : Set α))) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ ({t} : Set α))) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ ({t} : Set α))) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
        -- 3.6. substitute
        have s3_6 : s ∈ ({t} : Set α) := by
          have c1 : A ∩ f ⁻¹' (f '' (A ∩ ({t} : Set α))) = ({t} : Set α) := by first | exact (hD2 ({t} : Set α) (by parley_set_side)) | exact ((hD2 ({t} : Set α) (by parley_set_side))).symm | simpa using (hD2 ({t} : Set α) (by parley_set_side)) | exact_mod_cast (hD2 ({t} : Set α) (by parley_set_side)) | (have h := (hD2 ({t} : Set α) (by parley_set_side)); parley_set_side)
          have row1 : s ∈ ({t} : Set α) := by parley_subst_at c1 s3_5
          exact row1
        -- 3.7. def:singleton x := s, a := t, from 3.6
        have s3_7 : s = t := by first | exact ((Parley.Items.Stdlib.Sets.def_singleton (a := t) (x := s))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_singleton (a := t) (x := s))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_singleton (a := t) (x := s))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_singleton (a := t) (x := s))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_singleton (a := t) (x := s))).mp (by parley_set_side); parley_set_side)
        all_goals parley_set_side
      -- 4. def:one-to-one, from H3, 3
      have s4 : Set.MapsTo f A B ∧ Set.InjOn f A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := f) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := f) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Hammack.OneToOnePreimageOfImage.OneToOnePreimageOfImage

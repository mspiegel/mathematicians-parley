module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/preimage-of-image-of-preimage.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PreimageOfImageOfPreimage.PreimageOfImageOfPreimage

theorem preimage_of_image_of_preimage {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) (Y : Set α) (hH4 : Y ⊆ B) :
    A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y)) = A ∩ f ⁻¹' Y := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ f ⁻¹' Y, u ∈ A := by
    intro u hK1
    -- 1.1. def:preimage Z := Y, from K1
    have s1_1 : u ∈ A := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1; parley_set_side)
    all_goals exact s1_1
  -- 2. def:subset, from 1
  have s2 : A ∩ f ⁻¹' Y ⊆ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' Y) (Y := A))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' Y) (Y := A))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ u ∈ A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y)), u ∈ A ∩ f ⁻¹' Y := by
    intro u hK2
    -- 3.1. def:preimage Z := f[f⁻¹[Y]], from K2
    have s3_1a : u ∈ A := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1; parley_set_side)
    have s3_1b : f u ∈ f '' (A ∩ f ⁻¹' Y) := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2; parley_set_side)
    -- 3.2. obtain s: def:image u := f(u), Y := f⁻¹[Y], from 2, 3.1
    obtain ⟨s, s3_2a, s3_2b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := A ∩ f ⁻¹' Y) (f := f) (u := f u) (W := Set.univ) (by parley_set_side) s2)).mp (by parley_set_side)
    -- 3.3. def:preimage u := s, Z := Y, from 3.2
    have s3_3a : s ∈ A := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1; parley_set_side)
    have s3_3b : f s ∈ Y := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2; parley_set_side)
    -- 3.4. substitute f(u) = f(s) (line 3.2) into line 3.3
    have s3_4 : f u ∈ Y := by parley_subst_at s3_2b s3_3b
    -- 3.5. def:preimage Z := Y, from 3.1, 3.4
    have s3_5 : u ∈ A ∩ f ⁻¹' Y := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s3_5
  -- 4. def:subset, from 3
  have s4 : A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y)) ⊆ A ∩ f ⁻¹' Y := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y))) (Y := A ∩ f ⁻¹' Y))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y))) (Y := A ∩ f ⁻¹' Y))).mpr (by parley_set_side); parley_set_side)
  -- 5. proof
  have s5 : ∀ u ∈ A ∩ f ⁻¹' Y, u ∈ A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y)) := by
    intro u hK3
    -- 5.1. def:preimage Z := Y, from K3
    have s5_1a : u ∈ A := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1; parley_set_side)
    have s5_1b : f u ∈ Y := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2; parley_set_side)
    -- 5.2. mun:value-in-image Y := f⁻¹[Y], from K3, 2
    have s5_2 : f u ∈ f '' (A ∩ f ⁻¹' Y) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A ∩ f ⁻¹' Y) (f := f) (s := u) (W := Set.univ) (by parley_set_side) s2 hK3) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A ∩ f ⁻¹' Y) (f := f) (s := u) (W := Set.univ) (by parley_set_side) s2 hK3)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A ∩ f ⁻¹' Y) (f := f) (s := u) (W := Set.univ) (by parley_set_side) s2 hK3) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A ∩ f ⁻¹' Y) (f := f) (s := u) (W := Set.univ) (by parley_set_side) s2 hK3) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A ∩ f ⁻¹' Y) (f := f) (s := u) (W := Set.univ) (by parley_set_side) s2 hK3); parley_set_side)
    -- 5.3. def:preimage Z := f[f⁻¹[Y]], from 5.1, 5.2
    have s5_3 : u ∈ A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ f ⁻¹' Y)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s5_3
  -- 6. def:subset, from 5
  have s6 : A ∩ f ⁻¹' Y ⊆ A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' Y) (Y := A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y))))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' Y) (Y := A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y))))).mpr (by parley_set_side); parley_set_side)
  -- 7. mun:subset-antisymmetric, from 4, 6
  have s7 : A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y)) = A ∩ f ⁻¹' Y := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y))) (Y := A ∩ f ⁻¹' Y) s4 s6) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y))) (Y := A ∩ f ⁻¹' Y) s4 s6)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y))) (Y := A ∩ f ⁻¹' Y) s4 s6) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y))) (Y := A ∩ f ⁻¹' Y) s4 s6) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (f '' (A ∩ f ⁻¹' Y))) (Y := A ∩ f ⁻¹' Y) s4 s6); parley_set_side)
  all_goals exact s7

end Parley.Proofs.Hammack.PreimageOfImageOfPreimage.PreimageOfImageOfPreimage

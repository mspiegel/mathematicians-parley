module

public import Tactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/preimage-of-image.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage

theorem subset_of_preimage_of_image {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) (X : Set α) (hH4 : X ⊆ A) :
    X ⊆ A ∩ f ⁻¹' (f '' X) := by
  -- 1. proof
  have s1 : ∀ x ∈ X, x ∈ A ∩ f ⁻¹' (f '' X) := by
    intro x hK1
    -- 1.1. mun:in-subset, from H4, K1
    have s1_1 : x ∈ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := x) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := x) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := x) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := x) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := x) (by parley_side) (by parley_side)); parley_side)
    -- 1.2. mun:value-in-image, from H4, K1
    have s1_2 : f x ∈ f '' X := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := x) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := x) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := x) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := x) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := x) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := x) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side)); parley_side)
    -- 1.3. def:preimage u := x, from 1.1, 1.2
    have s1_3 : x ∈ A ∩ f ⁻¹' (f '' X) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' X) (f := f) (u := x) (W := Set.univ) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' X) (f := f) (u := x) (W := Set.univ) (by parley_side))).mpr (by parley_side); parley_side)
    all_goals parley_side
  -- 2. def:subset, from 1
  have s2 : X ⊆ A ∩ f ⁻¹' (f '' X) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := A ∩ f ⁻¹' (f '' X)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := A ∩ f ⁻¹' (f '' X)))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage

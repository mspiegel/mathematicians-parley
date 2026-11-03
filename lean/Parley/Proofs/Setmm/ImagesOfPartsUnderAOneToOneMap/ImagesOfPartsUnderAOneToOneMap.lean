module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Setmm.ImageOfAPointUnderAOneToOneMap.ImageOfAPointUnderAOneToOneMap

/-! Written from proofs/setmm/images-of-parts-under-a-one-to-one-map.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImagesOfPartsUnderAOneToOneMap.ImagesOfPartsUnderAOneToOneMap

theorem images_of_parts_under_a_one_to_one_map {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (C : Set α) (hH4 : C ⊆ A) (D : Set α) (hH5 : D ⊆ A) :
    (F '' C ⊆ F '' D ↔ C ⊆ D) := by
  -- the theorem. both directions
  have sThm : F '' C ⊆ F '' D ↔ C ⊆ D := by
    constructor
    · skip
      intro hD1
      -- 1. proof
      have s1 : ∀ t ∈ C, t ∈ D := by
        intro t hK1
        -- 1.1. mun:in-subset X := C, Y := A, u := t, from H4, K1
        have s1_1 : t ∈ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := C) (Y := A) (u := t) hH4 hK1) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := C) (Y := A) (u := t) hH4 hK1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := C) (Y := A) (u := t) hH4 hK1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := C) (Y := A) (u := t) hH4 hK1) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := C) (Y := A) (u := t) hH4 hK1); parley_set_side)
        -- 1.2. mun:value-in-image s := t, Y := C, from H4, K1
        have s1_2 : F t ∈ F '' C := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := C) (f := F) (s := t) (W := Set.univ) (by parley_set_side) hH4 hK1) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := C) (f := F) (s := t) (W := Set.univ) (by parley_set_side) hH4 hK1)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := C) (f := F) (s := t) (W := Set.univ) (by parley_set_side) hH4 hK1) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := C) (f := F) (s := t) (W := Set.univ) (by parley_set_side) hH4 hK1) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := C) (f := F) (s := t) (W := Set.univ) (by parley_set_side) hH4 hK1); parley_set_side)
        -- 1.3. mun:in-subset X := F[C], Y := F[D], u := F(t), from D1, 1.2
        have s1_3 : F t ∈ F '' D := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := F '' C) (Y := F '' D) (u := F t) hD1 s1_2) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := F '' C) (Y := F '' D) (u := F t) hD1 s1_2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := F '' C) (Y := F '' D) (u := F t) hD1 s1_2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := F '' C) (Y := F '' D) (u := F t) hD1 s1_2) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := F '' C) (Y := F '' D) (u := F t) hD1 s1_2); parley_set_side)
        -- 1.4. thm:image-of-a-point-under-a-one-to-one-map X := t, Y := D, from H3, H5, 1.1
        have s1_4 : F t ∈ F '' D ↔ t ∈ D := by first | exact (Parley.Proofs.Setmm.ImageOfAPointUnderAOneToOneMap.ImageOfAPointUnderAOneToOneMap.image_of_a_point_under_a_one_to_one_map (A := A) (B := B) (F := F) hH3 (X := t) s1_1 (Y := D) hH5) | exact ((Parley.Proofs.Setmm.ImageOfAPointUnderAOneToOneMap.ImageOfAPointUnderAOneToOneMap.image_of_a_point_under_a_one_to_one_map (A := A) (B := B) (F := F) hH3 (X := t) s1_1 (Y := D) hH5)).symm | simpa using (Parley.Proofs.Setmm.ImageOfAPointUnderAOneToOneMap.ImageOfAPointUnderAOneToOneMap.image_of_a_point_under_a_one_to_one_map (A := A) (B := B) (F := F) hH3 (X := t) s1_1 (Y := D) hH5) | exact_mod_cast (Parley.Proofs.Setmm.ImageOfAPointUnderAOneToOneMap.ImageOfAPointUnderAOneToOneMap.image_of_a_point_under_a_one_to_one_map (A := A) (B := B) (F := F) hH3 (X := t) s1_1 (Y := D) hH5) | (have h := (Parley.Proofs.Setmm.ImageOfAPointUnderAOneToOneMap.ImageOfAPointUnderAOneToOneMap.image_of_a_point_under_a_one_to_one_map (A := A) (B := B) (F := F) hH3 (X := t) s1_1 (Y := D) hH5); parley_set_side)
        -- 1.5. mun:iff-from-left P := F(t) ∈ F[D], Q := t ∈ D, from 1.3, 1.4
        have s1_5 : t ∈ D := by first | exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := F t ∈ F '' D) (Q := t ∈ D) s1_4 s1_3) | exact ((Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := F t ∈ F '' D) (Q := t ∈ D) s1_4 s1_3)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := F t ∈ F '' D) (Q := t ∈ D) s1_4 s1_3) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := F t ∈ F '' D) (Q := t ∈ D) s1_4 s1_3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := F t ∈ F '' D) (Q := t ∈ D) s1_4 s1_3); parley_set_side)
        all_goals exact s1_5
      -- 2. def:subset, from 1
      have s2 : C ⊆ D := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := C) (Y := D))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := C) (Y := D))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 3. mun:image-monotone Y := C, Z := D, from D2
      have s3 : F '' C ⊆ F '' D := by first | exact (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := C) (Z := D) (f := F) (X := Set.univ) (W := Set.univ) (by parley_set_side) hD2) | exact ((Parley.Items.Stdlib.Functions.mun_image_monotone (Y := C) (Z := D) (f := F) (X := Set.univ) (W := Set.univ) (by parley_set_side) hD2)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := C) (Z := D) (f := F) (X := Set.univ) (W := Set.univ) (by parley_set_side) hD2) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := C) (Z := D) (f := F) (X := Set.univ) (W := Set.univ) (by parley_set_side) hD2) | (have h := (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := C) (Z := D) (f := F) (X := Set.univ) (W := Set.univ) (by parley_set_side) hD2); parley_set_side)
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.ImagesOfPartsUnderAOneToOneMap.ImagesOfPartsUnderAOneToOneMap

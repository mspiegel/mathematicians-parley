module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/image-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImageOfUnion.ImageOfUnion

set_option maxHeartbeats 600000 in
theorem image_of_union {α : Type*} (A : Set α) (Y : Set α) (F : α → α) (hH3 : Set.MapsTo F A Y) (B : Set α) (hH4 : B ⊆ A) (C : Set α) (hH5 : C ⊆ A) :
    F '' (A ∩ (B ∪ C)) = F '' (A ∩ B) ∪ F '' (A ∩ C) := by
  -- 1. mun:union-subset, from H4, H5
  have s1 : B ∪ C ⊆ A := by first | exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := C) (Z := A) hH4 hH5) | exact ((Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := C) (Z := A) hH4 hH5)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := C) (Z := A) hH4 hH5) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := C) (Z := A) hH4 hH5) | (have h := (Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := C) (Z := A) hH4 hH5); parley_set_side)
  -- 2. proof
  have s2 : ∀ u ∈ F '' (A ∩ (B ∪ C)), u ∈ F '' (A ∩ B) ∪ F '' (A ∩ C) := by
    intro u hK1
    -- 2.1. def:image X := A, Y := B ∪ C, from K1, 1
    have s2_1 : ∃ s ∈ B ∪ C, u = F s := by first | exact ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B ∪ C) (f := F) (u := u) (W := Set.univ) s1 (by parley_set_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B ∪ C) (f := F) (u := u) (W := Set.univ) s1 (by parley_set_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B ∪ C) (f := F) (u := u) (W := Set.univ) s1 (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B ∪ C) (f := F) (u := u) (W := Set.univ) s1 (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B ∪ C) (f := F) (u := u) (W := Set.univ) s1 (by parley_set_side))).mp (by parley_set_side); parley_set_side)
    -- 2.2. obtain s from line 2.1
    obtain ⟨s, s2_2a, s2_2b⟩ := s2_1
    -- 2.3. def:union, from 2.2
    have s2_3 : s ∈ B ∨ s ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := s))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := s))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := s))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := s))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := s))).mp (by parley_set_side); parley_set_side)
    -- 2.4. cases, from 2.3
    have s2_4 : u ∈ F '' (A ∩ B) ∪ F '' (A ∩ C) := by
      rcases s2_3 with hC1 | hC2
      · skip
        -- 2.4.1. mun:value-in-image, from C1, H4
        have s2_4_1 : F s ∈ F '' (A ∩ B) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B) (f := F) (s := s) (W := Set.univ) hH4 hC1 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B) (f := F) (s := s) (W := Set.univ) hH4 hC1 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B) (f := F) (s := s) (W := Set.univ) hH4 hC1 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B) (f := F) (s := s) (W := Set.univ) hH4 hC1 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B) (f := F) (s := s) (W := Set.univ) hH4 hC1 (by parley_set_side)); parley_set_side)
        -- 2.4.2. substitute u = F(s) (line 2.2) into line 2.4.1
        have s2_4_2 : u ∈ F '' (A ∩ B) := by parley_subst_at s2_2b s2_4_1
        -- 2.4.3. mun:in-union-left, from 2.4.2
        have s2_4_3 : u ∈ F '' (A ∩ B) ∪ F '' (A ∩ C) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u) s2_4_2) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u) s2_4_2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u) s2_4_2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u) s2_4_2) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u) s2_4_2); parley_set_side)
        all_goals parley_set_side
      · skip
        -- 2.4.4. mun:value-in-image, from C2, H5
        have s2_4_4 : F s ∈ F '' (A ∩ C) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := C) (f := F) (s := s) (W := Set.univ) hH5 hC2 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := C) (f := F) (s := s) (W := Set.univ) hH5 hC2 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := C) (f := F) (s := s) (W := Set.univ) hH5 hC2 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := C) (f := F) (s := s) (W := Set.univ) hH5 hC2 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := C) (f := F) (s := s) (W := Set.univ) hH5 hC2 (by parley_set_side)); parley_set_side)
        -- 2.4.5. substitute u = F(s) (line 2.2) into line 2.4.4
        have s2_4_5 : u ∈ F '' (A ∩ C) := by parley_subst_at s2_2b s2_4_4
        -- 2.4.6. mun:in-union-right, from 2.4.5
        have s2_4_6 : u ∈ F '' (A ∩ B) ∪ F '' (A ∩ C) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u) s2_4_5) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u) s2_4_5)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u) s2_4_5) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u) s2_4_5) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u) s2_4_5); parley_set_side)
        all_goals parley_set_side
    all_goals exact s2_4
  -- 3. def:subset, from 2
  have s3 : F '' (A ∩ (B ∪ C)) ⊆ F '' (A ∩ B) ∪ F '' (A ∩ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := F '' (A ∩ (B ∪ C))) (Y := F '' (A ∩ B) ∪ F '' (A ∩ C)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := F '' (A ∩ (B ∪ C))) (Y := F '' (A ∩ B) ∪ F '' (A ∩ C)))).mpr (by parley_set_side); parley_set_side)
  -- 4. proof
  have s4 : ∀ u ∈ F '' (A ∩ B) ∪ F '' (A ∩ C), u ∈ F '' (A ∩ (B ∪ C)) := by
    intro u hK2
    -- 4.1. def:union, from K2
    have s4_1 : u ∈ F '' (A ∩ B) ∨ u ∈ F '' (A ∩ C) := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := F '' (A ∩ B)) (Z := F '' (A ∩ C)) (u := u))).mp (by parley_set_side); parley_set_side)
    -- 4.2. cases, from 4.1
    have s4_2 : u ∈ F '' (A ∩ (B ∪ C)) := by
      rcases s4_1 with hC3 | hC4
      · skip
        -- 4.2.1. def:image X := A, Y := B, from C3, H4
        have s4_2_1 : ∃ s ∈ B, u = F s := by first | exact ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B) (f := F) (u := u) (W := Set.univ) hH4 (by parley_set_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B) (f := F) (u := u) (W := Set.univ) hH4 (by parley_set_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B) (f := F) (u := u) (W := Set.univ) hH4 (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B) (f := F) (u := u) (W := Set.univ) hH4 (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B) (f := F) (u := u) (W := Set.univ) hH4 (by parley_set_side))).mp (by parley_set_side); parley_set_side)
        -- 4.2.2. obtain s from line 4.2.1
        obtain ⟨s, s4_2_2a, s4_2_2b⟩ := s4_2_1
        -- 4.2.3. mun:in-union-left, from 4.2.2
        have s4_2_3 : s ∈ B ∪ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := s) s4_2_2a) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := s) s4_2_2a)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := s) s4_2_2a) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := s) s4_2_2a) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := s) s4_2_2a); parley_set_side)
        -- 4.2.4. mun:value-in-image, from 1, 4.2.3
        have s4_2_4 : F s ∈ F '' (A ∩ (B ∪ C)) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B ∪ C) (f := F) (s := s) (W := Set.univ) s1 s4_2_3 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B ∪ C) (f := F) (s := s) (W := Set.univ) s1 s4_2_3 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B ∪ C) (f := F) (s := s) (W := Set.univ) s1 s4_2_3 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B ∪ C) (f := F) (s := s) (W := Set.univ) s1 s4_2_3 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B ∪ C) (f := F) (s := s) (W := Set.univ) s1 s4_2_3 (by parley_set_side)); parley_set_side)
        -- 4.2.5. substitute u = F(s) (line 4.2.2) into line 4.2.4
        have s4_2_5 : u ∈ F '' (A ∩ (B ∪ C)) := by parley_subst_at s4_2_2b s4_2_4
        all_goals parley_set_side
      · skip
        -- 4.2.6. def:image X := A, Y := C, from C4, H5
        have s4_2_6 : ∃ s ∈ C, u = F s := by first | exact ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := C) (f := F) (u := u) (W := Set.univ) hH5 (by parley_set_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := C) (f := F) (u := u) (W := Set.univ) hH5 (by parley_set_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := C) (f := F) (u := u) (W := Set.univ) hH5 (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := C) (f := F) (u := u) (W := Set.univ) hH5 (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := C) (f := F) (u := u) (W := Set.univ) hH5 (by parley_set_side))).mp (by parley_set_side); parley_set_side)
        -- 4.2.7. obtain s from line 4.2.6
        obtain ⟨s, s4_2_7a, s4_2_7b⟩ := s4_2_6
        -- 4.2.8. mun:in-union-right, from 4.2.7
        have s4_2_8 : s ∈ B ∪ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := s) s4_2_7a) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := s) s4_2_7a)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := s) s4_2_7a) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := s) s4_2_7a) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := s) s4_2_7a); parley_set_side)
        -- 4.2.9. mun:value-in-image, from 1, 4.2.8
        have s4_2_9 : F s ∈ F '' (A ∩ (B ∪ C)) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B ∪ C) (f := F) (s := s) (W := Set.univ) s1 s4_2_8 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B ∪ C) (f := F) (s := s) (W := Set.univ) s1 s4_2_8 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B ∪ C) (f := F) (s := s) (W := Set.univ) s1 s4_2_8 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B ∪ C) (f := F) (s := s) (W := Set.univ) s1 s4_2_8 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B ∪ C) (f := F) (s := s) (W := Set.univ) s1 s4_2_8 (by parley_set_side)); parley_set_side)
        -- 4.2.10. substitute u = F(s) (line 4.2.7) into line 4.2.9
        have s4_2_10 : u ∈ F '' (A ∩ (B ∪ C)) := by parley_subst_at s4_2_7b s4_2_9
        all_goals parley_set_side
    all_goals exact s4_2
  -- 5. def:subset, from 4
  have s5 : F '' (A ∩ B) ∪ F '' (A ∩ C) ⊆ F '' (A ∩ (B ∪ C)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := F '' (A ∩ B) ∪ F '' (A ∩ C)) (Y := F '' (A ∩ (B ∪ C))))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := F '' (A ∩ B) ∪ F '' (A ∩ C)) (Y := F '' (A ∩ (B ∪ C))))).mpr (by parley_set_side); parley_set_side)
  -- 6. mun:subset-antisymmetric, from 3, 5
  have s6 : F '' (A ∩ (B ∪ C)) = F '' (A ∩ B) ∪ F '' (A ∩ C) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F '' (A ∩ (B ∪ C))) (Y := F '' (A ∩ B) ∪ F '' (A ∩ C)) s3 s5) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F '' (A ∩ (B ∪ C))) (Y := F '' (A ∩ B) ∪ F '' (A ∩ C)) s3 s5)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F '' (A ∩ (B ∪ C))) (Y := F '' (A ∩ B) ∪ F '' (A ∩ C)) s3 s5) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F '' (A ∩ (B ∪ C))) (Y := F '' (A ∩ B) ∪ F '' (A ∩ C)) s3 s5) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F '' (A ∩ (B ∪ C))) (Y := F '' (A ∩ B) ∪ F '' (A ∩ C)) s3 s5); parley_set_side)
  all_goals exact s6

end Parley.Proofs.Setmm.ImageOfUnion.ImageOfUnion

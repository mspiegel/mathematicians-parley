module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/disjoint-within-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DisjointWithinDifference.DisjointWithinDifference

set_option maxHeartbeats 400000 in
theorem disjoint_within_difference {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ C) :
    (A ∩ B = ∅ ↔ A ⊆ C \ B) := by
  -- the theorem. both directions
  have sThm : A ∩ B = ∅ ↔ A ⊆ C \ B := by
    constructor
    · skip
      intro hD1
      -- 1. proof
      have s1 : ∀ t ∈ A, t ∈ C \ B := by
        intro t hK
        -- 1.1. mun:in-subset X := A, Y := C, u := t, from H4, K
        have s1_1 : t ∈ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) hH4 hK) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) hH4 hK)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) hH4 hK) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) hH4 hK) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) hH4 hK); parley_set_side)
        -- 1.2. mun:disjoint-member Y := A, Z := B, u := t, from D1, K
        have s1_2 : ¬ t ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) hD1 hK) | exact ((Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) hD1 hK)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) hD1 hK) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) hD1 hK) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) hD1 hK); parley_set_side)
        -- 1.3. def:difference u := t, Y := C, Z := B, from 1.1, 1.2
        have s1_3 : t ∈ C \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mpr (by parley_set_side); parley_set_side)
        all_goals exact s1_3
      -- 2. def:subset X := A, Y := C ∖ B, from 1
      have s2 : A ⊆ C \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 3. def:subset X := A, Y := C ∖ B, from D2
      have s3 : ∀ t ∈ A, t ∈ C \ B := by first | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp (by parley_set_side); parley_set_side)
      -- 4. proof
      have s4 : ∀ s ∈ A, ¬ s ∈ B := by
        intro s hK
        -- 4.1. instantiate t := s in line 3, from K
        have s4_1 : s ∈ C \ B := by first | exact (s3 s (by parley_set_side)) | exact ((s3 s (by parley_set_side))).symm | simpa using (s3 s (by parley_set_side)) | exact_mod_cast (s3 s (by parley_set_side)) | (have h := (s3 s (by parley_set_side)); parley_set_side)
        -- 4.2. def:difference u := s, Y := C, Z := B, from 4.1
        have s4_2 : s ∈ C ∧ ¬ s ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp (by parley_set_side); parley_set_side)
        -- 4.3. restate 4.2
        have s4_3 : ¬ s ∈ B := by parley_set_side
        all_goals exact s4_3
      -- 5. calculation
      have s5 : A ∩ B = ∅ := by
        calc A ∩ B = B ∩ A := by first | exact (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)) | exact ((Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)); parley_set_side)
          _ = ∅ := by first | exact (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) s4) | exact ((Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) s4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) s4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) s4) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) s4); parley_set_side)
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.DisjointWithinDifference.DisjointWithinDifference

module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-of-intersection-2.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetOfIntersection2.SubsetOfIntersection

theorem subset_of_intersection {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    (A ⊆ B ∧ A ⊆ C ↔ A ⊆ B ∩ C) := by
  -- the theorem. both directions
  have sThm : A ⊆ B ∧ A ⊆ C ↔ A ⊆ B ∩ C := by
    constructor
    · skip
      intro hD1
      -- 1. proof
      have s1 : ∀ u ∈ A, u ∈ B ∩ C := by
        intro u hK1
        -- 1.1. mun:in-subset X := A, Y := B, from D1, K1
        have s1_1 : u ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hD1.1 hK1) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hD1.1 hK1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hD1.1 hK1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hD1.1 hK1) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hD1.1 hK1); parley_set_side)
        -- 1.2. mun:in-subset X := A, Y := C, from D1, K1
        have s1_2 : u ∈ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := u) hD1.2 hK1) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := u) hD1.2 hK1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := u) hD1.2 hK1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := u) hD1.2 hK1) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := u) hD1.2 hK1); parley_set_side)
        -- 1.3. join 1.1, 1.2
        have s1_3 : u ∈ B ∧ u ∈ C := by parley_set_side
        -- 1.4. def:intersection, from 1.3
        have s1_4 : u ∈ B ∩ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mpr (by parley_set_side); parley_set_side)
        all_goals exact s1_4
      -- 2. def:subset, from 1
      have s2 : A ⊆ B ∩ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 3. proof
      have s3 : ∀ u ∈ A, u ∈ B ∧ u ∈ C := by
        intro u hK2
        -- 3.1. mun:in-subset X := A, Y := B ∩ C, from D2, K2
        have s3_1 : u ∈ B ∩ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∩ C) (u := u) hD2 hK2) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∩ C) (u := u) hD2 hK2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∩ C) (u := u) hD2 hK2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∩ C) (u := u) hD2 hK2) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∩ C) (u := u) hD2 hK2); parley_set_side)
        -- 3.2. def:intersection, from 3.1
        have s3_2 : u ∈ B ∧ u ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mp (by parley_set_side); parley_set_side)
        all_goals exact s3_2
      -- 4. proof
      have s4 : ∀ u ∈ A, u ∈ B := by
        intro u hK3
        -- 4.1. restate 3
        have s4_1 : u ∈ B := by parley_set_side
        all_goals exact s4_1
      -- 5. proof
      have s5 : ∀ u ∈ A, u ∈ C := by
        intro u hK4
        -- 5.1. restate 3
        have s5_1 : u ∈ C := by parley_set_side
        all_goals exact s5_1
      -- 6. def:subset, from 4
      have s6 : A ⊆ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr (by parley_set_side); parley_set_side)
      -- 7. def:subset X := A, Y := C, from 5
      have s7 : A ⊆ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mpr (by parley_set_side); parley_set_side)
      -- 8. join 6, 7
      have s8 : A ⊆ B ∧ A ⊆ C := by parley_set_side
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.SubsetOfIntersection2.SubsetOfIntersection

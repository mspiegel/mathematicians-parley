module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-of-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetOfIntersection.SubsetOfIntersection

theorem subset_of_intersection {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    (A ⊆ B ∧ A ⊆ C ↔ A ⊆ B ∩ C) := by
  -- the theorem. both directions
  have sThm : A ⊆ B ∧ A ⊆ C ↔ A ⊆ B ∩ C := by
    constructor
    · skip
      intro hD1
      -- 1. def:subset X := A, Y := B, from D1
      have s1 : ∀ t ∈ A, t ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mp (by parley_set_side); parley_set_side)
      -- 2. def:subset X := A, Y := C, from D1
      have s2 : ∀ t ∈ A, t ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp (by parley_set_side); parley_set_side)
      -- 3. proof
      have s3 : ∀ t ∈ A, t ∈ B ∩ C := by
        intro t hK
        -- 3.1. def:intersection u := t, from 1, 2
        have s3_1 : t ∈ B ∩ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mpr (by parley_set_side); parley_set_side)
        all_goals exact s3_1
      -- 4. def:subset X := A, Y := B ∩ C, from 3
      have s4 : A ⊆ B ∩ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 5. def:subset X := A, Y := B ∩ C, from D2
      have s5 : ∀ t ∈ A, t ∈ B ∩ C := by first | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mp (by parley_set_side); parley_set_side)
      -- 6. proof
      have s6 : ∀ t ∈ A, t ∈ B := by
        intro t hK
        -- 6.1. def:intersection u := t, from 5
        have s6_1 : t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).1; parley_set_side)
        all_goals exact s6_1
      -- 7. proof
      have s7 : ∀ t ∈ A, t ∈ C := by
        intro t hK
        -- 7.1. def:intersection u := t, from 5
        have s7_1 : t ∈ C := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).2; parley_set_side)
        all_goals exact s7_1
      -- 8. def:subset X := A, Y := B, from 6
      have s8 : A ⊆ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr (by parley_set_side); parley_set_side)
      -- 9. def:subset X := A, Y := C, from 7
      have s9 : A ⊆ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mpr (by parley_set_side); parley_set_side)
      -- 10. join 8, 9
      have s10 : A ⊆ B ∧ A ⊆ C := by parley_set_side
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.SubsetOfIntersection.SubsetOfIntersection

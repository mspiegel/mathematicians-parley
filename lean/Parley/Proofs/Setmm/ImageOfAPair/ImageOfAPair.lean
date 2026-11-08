module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/image-of-a-pair.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImageOfAPair.ImageOfAPair

set_option maxHeartbeats 600000 in
theorem image_of_a_pair {α : Type*} (A : Set α) (Y : Set α) (F : α → α) (hH3 : Set.MapsTo F A Y) (B : α) (hH4 : B ∈ A) (C : α) (hH5 : C ∈ A) :
    F '' (A ∩ ({B, C} : Set α)) = ({F B, F C} : Set α) := by
  -- 1. mun:pair-subset a := B, b := C, X := A, from H4, H5
  have s1 : ({B, C} : Set α) ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_pair_subset (X := A) (a := B) (b := C) hH4 hH5)
  -- 2. proof
  have s2 : ∀ u ∈ F '' (A ∩ ({B, C} : Set α)), u ∈ ({F B, F C} : Set α) := by
    intro u hK1
    -- 2.1. def:image X := A, Y := {B, C}, from K1, 1
    have s2_1 : ∃ s ∈ ({B, C} : Set α), u = F s := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := ({B, C} : Set α)) (f := F) (u := u) (W := Set.univ) s1 (by parley_set_side))).mp (by parley_set_side)
    -- 2.2. obtain s from line 2.1
    obtain ⟨s, s2_2a, s2_2b⟩ := s2_1
    -- 2.3. def:pair x := s, u := B, w := C, from 2.2
    have s2_3 : s = B ∨ s = C := ((Parley.Items.Stdlib.Sets.def_pair (u := B) (w := C) (x := s))).mp s2_2a
    -- 2.4. cases, from 2.3
    rcases s2_3 with hC1 | hC2
    · skip
      -- 2.4.1. substitute s = B (C1) into line 2.2
      have s2_4_1 : u = F B := by parley_subst_at hC1 s2_2b
      -- 2.4.2. mun:or-left, from 2.4.1
      have s2_4_2 : u = F B ∨ u = F C := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := u = F B) (Q := u = F C) s2_4_1)
      -- 2.4.3. def:pair x := u, u := F(B), w := F(C), from 2.4.2
      exact ((Parley.Items.Stdlib.Sets.def_pair (u := F B) (w := F C) (x := u))).mpr s2_4_2
    · skip
      -- 2.4.4. substitute s = C (C2) into line 2.2
      have s2_4_4 : u = F C := by parley_subst_at hC2 s2_2b
      -- 2.4.5. mun:or-right, from 2.4.4
      have s2_4_5 : u = F B ∨ u = F C := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := u = F B) (Q := u = F C) s2_4_4)
      -- 2.4.6. def:pair x := u, u := F(B), w := F(C), from 2.4.5
      exact ((Parley.Items.Stdlib.Sets.def_pair (u := F B) (w := F C) (x := u))).mpr s2_4_5
  -- 3. def:subset, from 2
  have s3 : F '' (A ∩ ({B, C} : Set α)) ⊆ ({F B, F C} : Set α) := ((Parley.Items.Stdlib.Sets.def_subset (X := F '' (A ∩ ({B, C} : Set α))) (Y := ({F B, F C} : Set α)))).mpr s2
  -- 4. proof
  have s4 : ∀ u ∈ ({F B, F C} : Set α), u ∈ F '' (A ∩ ({B, C} : Set α)) := by
    intro u hK2
    -- 4.1. def:pair x := u, u := F(B), w := F(C), from K2
    have s4_1 : u = F B ∨ u = F C := ((Parley.Items.Stdlib.Sets.def_pair (u := F B) (w := F C) (x := u))).mp hK2
    -- 4.2. cases, from 4.1
    rcases s4_1 with hC3 | hC4
    · skip
      -- 4.2.1. inspection
      have s4_2_1 : B ∈ ({B, C} : Set α) := by parley_set_side
      -- 4.2.2. mun:value-in-image, from 1, 4.2.1
      have s4_2_2 : F B ∈ F '' (A ∩ ({B, C} : Set α)) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := B) (W := Set.univ) s1 s4_2_1 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := B) (W := Set.univ) s1 s4_2_1 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := B) (W := Set.univ) s1 s4_2_1 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := B) (W := Set.univ) s1 s4_2_1 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := B) (W := Set.univ) s1 s4_2_1 (by parley_set_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := B) (W := Set.univ) s1 s4_2_1 (by parley_set_side)); parley_set_side)
      -- 4.2.3. substitute u = F(B) (C3) into line 4.2.2
      parley_subst_at hC3 s4_2_2
    · skip
      -- 4.2.4. inspection
      have s4_2_4 : C ∈ ({B, C} : Set α) := by parley_set_side
      -- 4.2.5. mun:value-in-image, from 1, 4.2.4
      have s4_2_5 : F C ∈ F '' (A ∩ ({B, C} : Set α)) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := C) (W := Set.univ) s1 s4_2_4 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := C) (W := Set.univ) s1 s4_2_4 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := C) (W := Set.univ) s1 s4_2_4 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := C) (W := Set.univ) s1 s4_2_4 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := C) (W := Set.univ) s1 s4_2_4 (by parley_set_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := ({B, C} : Set α)) (f := F) (s := C) (W := Set.univ) s1 s4_2_4 (by parley_set_side)); parley_set_side)
      -- 4.2.6. substitute u = F(C) (C4) into line 4.2.5
      parley_subst_at hC4 s4_2_5
  -- 5. def:subset, from 4
  have s5 : ({F B, F C} : Set α) ⊆ F '' (A ∩ ({B, C} : Set α)) := ((Parley.Items.Stdlib.Sets.def_subset (X := ({F B, F C} : Set α)) (Y := F '' (A ∩ ({B, C} : Set α))))).mpr s4
  -- 6. mun:subset-antisymmetric, from 3, 5
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F '' (A ∩ ({B, C} : Set α))) (Y := ({F B, F C} : Set α)) s3 s5)

end Parley.Proofs.Setmm.ImageOfAPair.ImageOfAPair

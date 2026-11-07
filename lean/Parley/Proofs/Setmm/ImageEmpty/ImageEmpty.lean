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

/-! Written from proofs/setmm/image-empty.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImageEmpty.ImageEmpty

set_option maxHeartbeats 400000 in
theorem image_empty {α : Type*} (A : Set α) (Y : Set α) (F : α → α) (hH2 : Set.MapsTo F A Y) (B : Set α) (hH3 : B ⊆ A) :
    (F '' (A ∩ B) = ∅ ↔ B = ∅) := by
  -- the theorem. both directions
  have sThm : F '' (A ∩ B) = ∅ ↔ B = ∅ := by
    constructor
    · skip
      intro hD1
      -- 1. proof
      have s1 : ∀ t ∈ B, t ∈ (∅ : Set α) := by
        intro t hK1
        -- 1.1. mun:value-in-image, from H3, K1
        have s1_1 : F t ∈ F '' (A ∩ B) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B) (f := F) (s := t) (W := Set.univ) hH3 hK1 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B) (f := F) (s := t) (W := Set.univ) hH3 hK1 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B) (f := F) (s := t) (W := Set.univ) hH3 hK1 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B) (f := F) (s := t) (W := Set.univ) hH3 hK1 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B) (f := F) (s := t) (W := Set.univ) hH3 hK1 (by parley_set_side)); parley_set_side)
        -- 1.2. substitute F[B] = ∅ (D1) into line 1.1
        have s1_2 : F t ∈ (∅ : Set α) := by parley_subst_at hD1 s1_1
        -- 1.3. inspection
        have s1_3 : ¬ F t ∈ (∅ : Set α) := by parley_set_side
        all_goals parley_set_side
      -- 2. def:subset, from 1
      have s2 : B ⊆ ∅ := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := B) (Y := ∅))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := B) (Y := ∅))).mpr (by parley_set_side); parley_set_side)
      -- 3. mun:subset-empty, from 2
      have s3 : B = ∅ := by first | exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := B))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := B))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := B))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := B))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := B))).mp (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 4. proof
      have s4 : ∀ u ∈ F '' (A ∩ B), u ∈ (∅ : Set α) := by
        intro u hK2
        -- 4.1. def:image, from H3, K2
        have s4_1 : ∃ s ∈ B, u = F s := by first | exact ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B) (f := F) (u := u) (W := Set.univ) hH3 (by parley_set_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B) (f := F) (u := u) (W := Set.univ) hH3 (by parley_set_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B) (f := F) (u := u) (W := Set.univ) hH3 (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B) (f := F) (u := u) (W := Set.univ) hH3 (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B) (f := F) (u := u) (W := Set.univ) hH3 (by parley_set_side))).mp (by parley_set_side); parley_set_side)
        -- 4.2. obtain s from line 4.1
        obtain ⟨s, s4_2a, s4_2b⟩ := s4_1
        -- 4.3. substitute B = ∅ (D2) into line 4.2
        have s4_3 : s ∈ (∅ : Set α) := by parley_subst_at hD2 s4_2a
        -- 4.4. inspection
        have s4_4 : ¬ s ∈ (∅ : Set α) := by parley_set_side
        all_goals parley_set_side
      -- 5. def:subset, from 4
      have s5 : F '' (A ∩ B) ⊆ ∅ := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := F '' (A ∩ B)) (Y := ∅))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := F '' (A ∩ B)) (Y := ∅))).mpr (by parley_set_side); parley_set_side)
      -- 6. mun:subset-empty, from 5
      have s6 : F '' (A ∩ B) = ∅ := by first | exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := F '' (A ∩ B)))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := F '' (A ∩ B)))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := F '' (A ∩ B)))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := F '' (A ∩ B)))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := F '' (A ∩ B)))).mp (by parley_set_side); parley_set_side)
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.ImageEmpty.ImageEmpty

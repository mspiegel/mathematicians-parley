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

/-! Written from proofs/setmm/image-of-a-point-under-a-one-to-one-map.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImageOfAPointUnderAOneToOneMap.ImageOfAPointUnderAOneToOneMap

theorem image_of_a_point_under_a_one_to_one_map {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (X : α) (hH4 : X ∈ A) (Y : Set α) (hH5 : Y ⊆ A) :
    (F X ∈ F '' (A ∩ Y) ↔ X ∈ Y) := by
  -- 1. def:one-to-one, from H3
  have s1a : Set.MapsTo F A B := (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := F) (by parley_set_side))).mp hH3).1
  have s1b : ∀ s ∈ A, ∀ t ∈ A, F s = F t → s = t := (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := F) (by parley_set_side))).mp hH3).2
  -- 2. both directions
  constructor
  · skip
    intro hD1
    -- 2.1. obtain s: def:image u := F(X), from D1, H5
    obtain ⟨s, s2_1a, s2_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := Y) (f := F) (u := F X) (W := Set.univ) hH5 (by parley_set_side))).mp (by parley_set_side)
    -- 2.2. mun:in-subset X := Y, Y := A, u := s, from H5, 2.1
    have s2_2 : s ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := Y) (Y := A) (u := s) hH5 s2_1a)
    -- 2.3. instantiate s := X, t := s in line 1, from H4, 2.1, 2.2
    have s2_3 : X = s := by first | exact (s1b X (by parley_set_side) s (by parley_set_side) (by parley_set_side)) | exact ((s1b X (by parley_set_side) s (by parley_set_side) (by parley_set_side))).symm | simpa using (s1b X (by parley_set_side) s (by parley_set_side) (by parley_set_side)) | exact_mod_cast (s1b X (by parley_set_side) s (by parley_set_side) (by parley_set_side)) | (have h := (s1b X (by parley_set_side) s (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 2.4. substitute X = s (line 2.3) into line 2.1
    parley_subst_at s2_3 s2_1a
  · skip
    intro hD2
    -- 2.5. mun:value-in-image s := X, from D2, H5
    first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := Y) (f := F) (s := X) (W := Set.univ) hH5 hD2 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := Y) (f := F) (s := X) (W := Set.univ) hH5 hD2 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := Y) (f := F) (s := X) (W := Set.univ) hH5 hD2 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := Y) (f := F) (s := X) (W := Set.univ) hH5 hD2 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := Y) (f := F) (s := X) (W := Set.univ) hH5 hD2 (by parley_set_side)); parley_set_side)

end Parley.Proofs.Setmm.ImageOfAPointUnderAOneToOneMap.ImageOfAPointUnderAOneToOneMap

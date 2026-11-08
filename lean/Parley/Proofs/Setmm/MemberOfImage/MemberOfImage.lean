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

/-! Written from proofs/setmm/member-of-image.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MemberOfImage.MemberOfImage

theorem member_of_image {α : Type*} (A : Set α) (B : Set α) (y : α) (F : α → α) (hH3 : Set.MapsTo F A B) (X : Set α) (hH4 : X ⊆ A) :
    (y ∈ F '' (A ∩ X) ↔ (∃ x ∈ X, F x = y)) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. obtain x: def:image u := y, from D1, H4
    obtain ⟨x, s1a, s1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := X) (f := F) (u := y) (W := Set.univ) hH4 (by parley_set_side))).mp (by parley_set_side)
    -- 2. exhibit, from 1
    exact ⟨x, by parley_set_side, by parley_set_side⟩
  · skip
    intro hD2
    -- 3. obtain x from D2
    obtain ⟨x, s3a, s3b⟩ := hD2
    -- 4. mun:value-in-image Y := X, s := x, from H4, 3
    have s4 : F x ∈ F '' (A ∩ X) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) hH4 s3a (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) hH4 s3a (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) hH4 s3a (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) hH4 s3a (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) hH4 s3a (by parley_set_side)); parley_set_side)
    -- 5. substitute F(x) = y (line 3) into line 4
    parley_subst_at s3b s4

end Parley.Proofs.Setmm.MemberOfImage.MemberOfImage

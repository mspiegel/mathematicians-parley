module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/setmm/member-of-image.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MemberOfImage.MemberOfImage

theorem member_of_image {α : Type*} (A : Set α) (B : Set α) (y : α) (F : α → α) (hH3 : Set.MapsTo F A B) (X : Set α) (hH4 : X ⊆ A) :
    (y ∈ F '' (A ∩ X) ↔ (∃ x ∈ X, F x = y)) := by
  -- the theorem. both directions
  have sThm : y ∈ F '' (A ∩ X) ↔ (∃ x ∈ X, F x = y) := by
    constructor
    · skip
      intro hD1
      -- 1. obtain x: def:image u := y, from D1, H4
      obtain ⟨x, s1a, s1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := X) (f := F) (u := y) (W := Set.univ) (by parley_set_side) hH4)).mp (by parley_set_side)
      -- 2. exhibit, from 1
      have s2 : ∃ x ∈ X, F x = y := ⟨x, by parley_set_side, by parley_set_side⟩
      all_goals parley_set_side
    · skip
      intro hD2
      -- 3. obtain x from D2
      obtain ⟨x, s3a, s3b⟩ := hD2
      -- 4. mun:value-in-image Y := X, s := x, from H4, 3
      have s4 : F x ∈ F '' (A ∩ X) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) (by parley_set_side) hH4 s3a) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) (by parley_set_side) hH4 s3a)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) (by parley_set_side) hH4 s3a) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) (by parley_set_side) hH4 s3a) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) (by parley_set_side) hH4 s3a); parley_set_side)
      -- 5. substitute F(x) = y (line 3) into line 4
      have s5 : y ∈ F '' (A ∩ X) := by parley_subst_at s3b s4
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.MemberOfImage.MemberOfImage

module

public import Functions
public import SetTactics
public import Tactics
public import Parley.Proofs.Setmm.InverseOfValue.InverseOfValue
public import Parley.Proofs.Setmm.ValueOfInverse.ValueOfInverse

/-! Written from proofs/setmm/value-and-inverse-agree.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ValueAndInverseAgree.ValueAndInverseAgree

theorem value_and_inverse_agree {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (hH4 : F '' (A ∩ A) = B) (C : α) (hH5 : C ∈ A) (D : α) (hH6 : D ∈ B) :
    (F C = D ↔ LeanBridges.Functions.inverse F A D = C) := by
  -- the theorem. both directions
  have sThm : F C = D ↔ LeanBridges.Functions.inverse F A D = C := by
    constructor
    · skip
      intro hD1
      -- 1. thm:inverse-of-value, from H3, H4, H5
      have s1 : LeanBridges.Functions.inverse F A (F C) = C := by first | exact (Parley.Proofs.Setmm.InverseOfValue.InverseOfValue.inverse_of_value (A := A) (B := B) (F := F) hH3 hH4 (C := C) hH5) | exact ((Parley.Proofs.Setmm.InverseOfValue.InverseOfValue.inverse_of_value (A := A) (B := B) (F := F) hH3 hH4 (C := C) hH5)).symm | simpa using (Parley.Proofs.Setmm.InverseOfValue.InverseOfValue.inverse_of_value (A := A) (B := B) (F := F) hH3 hH4 (C := C) hH5) | exact_mod_cast (Parley.Proofs.Setmm.InverseOfValue.InverseOfValue.inverse_of_value (A := A) (B := B) (F := F) hH3 hH4 (C := C) hH5) | (have h := (Parley.Proofs.Setmm.InverseOfValue.InverseOfValue.inverse_of_value (A := A) (B := B) (F := F) hH3 hH4 (C := C) hH5); parley_set_side)
      -- 2. substitute F(C) = D (D1) into line 1
      have s2 : LeanBridges.Functions.inverse F A D = C := by parley_subst_at hD1 s1
      all_goals parley_set_side
    · skip
      intro hD2
      -- 3. thm:value-of-inverse C := D, from H3, H4, H6
      have s3 : F (LeanBridges.Functions.inverse F A D) = D := by first | exact (Parley.Proofs.Setmm.ValueOfInverse.ValueOfInverse.value_of_inverse (A := A) (B := B) (F := F) hH3 hH4 (C := D) hH6) | exact ((Parley.Proofs.Setmm.ValueOfInverse.ValueOfInverse.value_of_inverse (A := A) (B := B) (F := F) hH3 hH4 (C := D) hH6)).symm | simpa using (Parley.Proofs.Setmm.ValueOfInverse.ValueOfInverse.value_of_inverse (A := A) (B := B) (F := F) hH3 hH4 (C := D) hH6) | exact_mod_cast (Parley.Proofs.Setmm.ValueOfInverse.ValueOfInverse.value_of_inverse (A := A) (B := B) (F := F) hH3 hH4 (C := D) hH6) | (have h := (Parley.Proofs.Setmm.ValueOfInverse.ValueOfInverse.value_of_inverse (A := A) (B := B) (F := F) hH3 hH4 (C := D) hH6); parley_set_side)
      -- 4. substitute F⁻¹(D) = C (D2) into line 3
      have s4 : F C = D := by parley_subst_at hD2 s3
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.ValueAndInverseAgree.ValueAndInverseAgree

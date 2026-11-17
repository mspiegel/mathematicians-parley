module

public import Functions
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Proofs.Setmm.InverseOfValue.InverseOfValue
public import Parley.Proofs.Setmm.ValueOfInverse.ValueOfInverse

/-! Written from proofs/setmm/value-and-inverse-agree.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ValueAndInverseAgree.ValueAndInverseAgree

theorem value_and_inverse_agree {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (B : Set β) (F : α → β) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (hH4 : F '' (A ∩ A) = B) (C : α) (hH5 : C ∈ A) (D : β) (hH6 : D ∈ B) :
    (F C = D ↔ LeanBridges.Functions.inverse F A D = C) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. thm:inverse-of-value, from H3, H4, H5
    have s1 : LeanBridges.Functions.inverse F A (F C) = C := by exact (Parley.Proofs.Setmm.InverseOfValue.InverseOfValue.inverse_of_value (A := A) (B := B) (F := F) hH3 hH4 (C := C) hH5)
    -- 2. substitute F(C) = D (D1) into line 1
    exact Eq.subst (motive := (fun t : β => LeanBridges.Functions.inverse F A t = C)) hD1 s1
  · skip
    intro hD2
    -- 3. thm:value-of-inverse C := D, from H3, H4, H6
    have s3 : F (LeanBridges.Functions.inverse F A D) = D := by exact (Parley.Proofs.Setmm.ValueOfInverse.ValueOfInverse.value_of_inverse (A := A) (B := B) (F := F) hH3 hH4 (C := D) hH6)
    -- 4. substitute F⁻¹(D) = C (D2) into line 3
    exact Eq.subst (motive := (fun t : α => F t = D)) hD2 s3

end Parley.Proofs.Setmm.ValueAndInverseAgree.ValueAndInverseAgree

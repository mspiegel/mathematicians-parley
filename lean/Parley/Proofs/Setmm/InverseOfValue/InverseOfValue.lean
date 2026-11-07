module

public import Functions
public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/setmm/inverse-of-value.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.InverseOfValue.InverseOfValue

theorem inverse_of_value {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (hH4 : F '' (A ∩ A) = B) (C : α) (hH5 : C ∈ A) :
    LeanBridges.Functions.inverse F A (F C) = C := by
  -- 1. mun:inverse-value g := F, y := C, from H3, H5
  have s1 : LeanBridges.Functions.inverse F A (F C) = C := by exact (Parley.Items.Stdlib.Functions.mun_inverse_value (X := B) (Y := A) (g := F) (y := C) hH3 hH5)
  all_goals exact s1

end Parley.Proofs.Setmm.InverseOfValue.InverseOfValue

module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/setmm/equal-values.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.EqualValues.EqualValues

theorem equal_values {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (C : α) (hH4 : C ∈ A) (D : α) (hH5 : D ∈ A) :
    (F C = F D ↔ C = D) := by
  -- 1. def:one-to-one, from H3
  have s1 : ∀ s ∈ A, ∀ t ∈ A, F s = F t → s = t := by exact (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := F) (by parley_set_side))).mp hH3).2
  -- 2. both directions
  constructor
  · skip
    intro hD1
    -- 2.1. instantiate s := C, t := D in line 1, from D1, H4, H5
    exact (s1 C (by parley_set_side) D (by parley_set_side) (by parley_set_side))
  · skip
    intro hD2
    -- 2.2. substitute C = D (D2)
    parley_subst hD2

end Parley.Proofs.Setmm.EqualValues.EqualValues

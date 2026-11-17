module

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
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/setmm/equal-values.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.EqualValues.EqualValues

theorem equal_values {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (B : Set β) (F : α → β) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (C : α) (hH4 : C ∈ A) (D : α) (hH5 : D ∈ A) :
    (F C = F D ↔ C = D) := by
  -- 1. def:one-to-one, from H3
  have s1 : ∀ s ∈ A, ∀ t ∈ A, F s = F t → s = t := by exact (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := F) hH3.1)).mp hH3).2
  -- 2. both directions
  constructor
  · skip
    intro hD1
    -- 2.1. instantiate s := C, t := D in line 1, from D1, H4, H5
    exact (s1 C hH4 D hH5 hD1)
  · skip
    intro hD2
    -- 2.2. substitute C = D (D2)
    exact congrArg (fun t : α => F t) hD2

end Parley.Proofs.Setmm.EqualValues.EqualValues

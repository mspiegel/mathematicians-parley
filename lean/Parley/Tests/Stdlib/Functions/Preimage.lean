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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from tests/stdlib/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Functions.Preimage

theorem preimage {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (B : Set β) (C : Set β) (f : α → β) (hH4 : Set.MapsTo f A B) (x : α) (hH5 : x ∈ A) (hH6 : f x ∈ C) :
    x ∈ A ∩ f ⁻¹' C := by
  -- 1. def:functions-preimage u := x, from H5, H6
  exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := C) (f := f) (u := x) (W := B) hH4)).mpr ⟨hH5, hH6⟩

end Parley.Tests.Stdlib.Functions.Preimage

module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from tests/stdlib/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Functions.Preimage

theorem preimage {α : Type*} (A : Set α) (B : Set α) (C : Set α) (f : α → α) (hH4 : Set.MapsTo f A B) (x : α) (hH5 : x ∈ A) (hH6 : f x ∈ C) :
    x ∈ A ∩ f ⁻¹' C := by
  -- 1. def:functions-preimage u := x, from H5, H6
  exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := C) (f := f) (u := x) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side)

end Parley.Tests.Stdlib.Functions.Preimage

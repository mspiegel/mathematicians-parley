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

namespace Parley.Tests.Stdlib.Functions.CompositionFunction

theorem composition_function {α : Type*} (A : Set α) (B : Set α) (C : Set α) (f : α → α) (hH4 : Set.MapsTo f A B) (g : α → α) (hH5 : Set.MapsTo g B C) :
    Set.MapsTo (g ∘ f) A C := by
  -- 1. mun:functions-composition-function
  exact (Parley.Items.Stdlib.Functions.mun_composition_function (Y := B) (W := C) (X := A) (f := f) (g := g) hH4 hH5)

end Parley.Tests.Stdlib.Functions.CompositionFunction

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
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

/-! Written from tests/stdlib/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Functions.CompositionValue

theorem composition_value {α : Type*} (A : Set α) (B : Set α) (C : Set α) (f : α → α) (hH4 : Set.MapsTo f A B) (g : α → α) (hH5 : Set.MapsTo g B C) (a : α) (hH6 : a ∈ A) :
    (g ∘ f) a = g (f a) := by
  -- 1. mun:functions-composition-value x := a, from H6
  exact (Parley.Items.Stdlib.Functions.mun_composition_value (Y := B) (X := A) (f := f) (g := g) (x := a) (W := Set.univ) hH6 hH4 (Set.mapsTo_univ _ _))

end Parley.Tests.Stdlib.Functions.CompositionValue

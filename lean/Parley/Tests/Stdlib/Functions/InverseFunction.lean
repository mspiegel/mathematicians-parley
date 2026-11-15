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
public import Parley.Items.Stdlib.Functions

/-! Written from tests/stdlib/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Functions.InverseFunction

theorem inverse_function {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B ∧ Set.InjOn f A) (hH4 : f '' (A ∩ A) = B) :
    Set.MapsTo (LeanBridges.Functions.inverse f A) B A := by
  -- 1. mun:functions-inverse-function, from H3, H4
  exact (Parley.Items.Stdlib.Functions.mun_inverse_function (X := A) (Y := B) (f := f) hH3 hH4)

end Parley.Tests.Stdlib.Functions.InverseFunction

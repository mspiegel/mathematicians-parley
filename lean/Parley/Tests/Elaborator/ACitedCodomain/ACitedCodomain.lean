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

/-! Written from tests/elaborator/a-cited-codomain.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedCodomain.ACitedCodomain

theorem a_cited_codomain {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (C : Set β) (B : β) (F : α → β) (hH4 : Set.MapsTo F A ({B} : Set β)) :
    (Set.MapsTo F A C ∧ Set.InjOn F A → (∀ s ∈ A, ∀ t ∈ A, F s = F t → s = t)) := by
  -- 1. proof
  intro hS
  -- 1.1. def:one-to-one f := F, from S
  exact (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := C) (f := F) hS.1)).mp hS).2

end Parley.Tests.Elaborator.ACitedCodomain.ACitedCodomain

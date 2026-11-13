module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
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
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.Extensionality

theorem extensionality {α : Type*} (A : Set α) (B : Set α) (hH3 : ∀ x ∈ A, x ∈ B) (hH4 : ∀ x ∈ B, x ∈ A) :
    A = B := by
  -- 1. axi:sets-extensionality X := A, Y := B, from H3, H4
  exact (Parley.Items.Stdlib.Sets.axi_extensionality (X := A) (Y := B) hH3 hH4)

end Parley.Tests.Stdlib.Sets.Extensionality

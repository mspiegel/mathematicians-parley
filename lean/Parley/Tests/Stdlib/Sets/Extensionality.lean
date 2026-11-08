module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
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

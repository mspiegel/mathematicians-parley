module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/notations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Notations.AMemberOfANonemptySet

theorem a_member_of_a_nonempty_set {α : Type*} (X : Set α) (k : ℤ) (hH2 : 0 ≤ k) (hH3 : (X.ncard : ℤ) = k + 1) :
    (∃ a ∈ X, True) := by
  -- 1. mun:card-nonempty, from H3
  exact (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) hH2 (by parley_set_side))

end Parley.Tests.Elaborator.Notations.AMemberOfANonemptySet

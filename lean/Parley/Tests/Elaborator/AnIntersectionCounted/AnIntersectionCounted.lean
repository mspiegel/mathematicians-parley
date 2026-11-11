module

public import SetTactics
public import Tactics
public import Mathlib.Data.ENat.Defs
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

/-! Written from tests/elaborator/an-intersection-counted.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIntersectionCounted.AnIntersectionCounted

theorem an_intersection_counted {α : Type*} (A : Set α) (B : Set α) (D : Set α) (m : ℤ) (hH4 : 0 ≤ m) (n : ℤ) (hH5 : 0 ≤ n) (hH6 : (A ∩ B).encard = ((m.toNat : ℕ) : ℕ∞)) (hH7 : D.encard = ((n.toNat : ℕ) : ℕ∞)) (hH8 : (A ∩ B) ∩ D = ∅) :
    ((A ∩ B ∪ D).ncard : ℤ) = m + n := by
  -- 1. mun:card-disjoint-union X := A ∩ B, Y := D, from H6, H7, H8
  exact (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) hH4 (n := n) hH5 (by parley_set_side) (by parley_set_side) hH8)

end Parley.Tests.Elaborator.AnIntersectionCounted.AnIntersectionCounted

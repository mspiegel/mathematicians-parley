module

public import SetTactics
public import Tactics
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/notations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Notations.AMemberOfANonemptySet

theorem a_member_of_a_nonempty_set {α : Type*} (X : Set α) (k : ℤ) (hH2 : 0 ≤ k) (hH3 : X.encard = (((k + 1).toNat : ℕ) : ℕ∞)) :
    (∃ a ∈ X, True) := by
  -- 1. mun:card-nonempty, from H3
  have s1 : ∃ a ∈ X, True := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) (by parley_set_side) hH3) | exact ((Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) (by parley_set_side) hH3)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) (by parley_set_side) hH3) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) (by parley_set_side) hH3) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) (by parley_set_side) hH3); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.Notations.AMemberOfANonemptySet

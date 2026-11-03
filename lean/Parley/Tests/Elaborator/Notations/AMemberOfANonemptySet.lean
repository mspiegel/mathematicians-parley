module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/notations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Notations.AMemberOfANonemptySet

theorem a_member_of_a_nonempty_set {α : Type*} (X : Set α) (k : ℕ) (hH3 : X.encard = ((k + 1 : ℕ) : ℕ∞)) :
    (∃ a ∈ X, True) := by
  -- 1. mun:card-nonempty, from H3
  have s1 : ∃ a ∈ X, True := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.Notations.AMemberOfANonemptySet

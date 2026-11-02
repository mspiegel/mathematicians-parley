module

public import LeanBridges
public import Parley.Items.Stdlib.Counting

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.SizeOfEmpty

theorem size_of_empty {α : Type*} :
    (∅ : Set α).encard = ((0 : ℕ) : ℕ∞) := by
  -- 1. mun:card-empty
  have s1 : (∅ : Set α).encard = ((0 : ℕ) : ℕ∞) := by first | exact Parley.Items.Stdlib.Counting.mun_card_empty | exact (Parley.Items.Stdlib.Counting.mun_card_empty).symm | simpa using Parley.Items.Stdlib.Counting.mun_card_empty | exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_side)
  all_goals parley_side

end Parley.Tests.Notations.Counting.SizeOfEmpty

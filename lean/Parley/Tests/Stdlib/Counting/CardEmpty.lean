module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.CardEmpty

theorem card_empty {α : Type*} :
    (∅ : Set α).encard = ((0 : ℕ) : ℕ∞) := by
  -- 1. mun:counting-card-empty
  have s1 : (∅ : Set α).encard = ((0 : ℕ) : ℕ∞) := by first | exact Parley.Items.Stdlib.Counting.mun_card_empty | exact (Parley.Items.Stdlib.Counting.mun_card_empty).symm | simpa using Parley.Items.Stdlib.Counting.mun_card_empty | exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_set_side)
  all_goals parley_set_side

end Parley.Tests.Stdlib.Counting.CardEmpty

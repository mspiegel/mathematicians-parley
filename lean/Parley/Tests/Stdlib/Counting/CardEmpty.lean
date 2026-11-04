module

public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.CardEmpty

theorem card_empty {α : Type*} :
    ((∅ : Set α).ncard : ℤ) = 0 := by
  -- 1. mun:counting-card-empty
  have s1 : ((∅ : Set α).ncard : ℤ) = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.mun_card_empty | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_empty).symm | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.CardEmpty

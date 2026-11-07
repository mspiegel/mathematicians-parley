module

public import NormTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.SizeOfEmpty

theorem size_of_empty {α : Type*} :
    ((∅ : Set α).ncard : ℤ) = 0 := by
  -- 1. mun:card-empty
  have s1 : ((∅ : Set α).ncard : ℤ) = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.mun_card_empty | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty) | exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_empty).symm | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_set_side)
  all_goals exact s1

end Parley.Tests.Notations.Counting.SizeOfEmpty

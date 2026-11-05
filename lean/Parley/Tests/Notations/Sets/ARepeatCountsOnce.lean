module

public import ArithTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.ARepeatCountsOnce

theorem a_repeat_counts_once :
    ({(1 : ℤ), (2 : ℤ), (2 : ℤ)} : Set ℤ).encard = ((2 : ℕ) : ℕ∞) := by
  -- 1. mun:listed-repeat a := 1, b := 2
  have s1 : ({(1 : ℤ), (2 : ℤ), (2 : ℤ)} : Set ℤ) = ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sets.mun_listed_repeat (a := (1 : ℤ)) (b := (2 : ℤ))) | exact ((Parley.Items.Stdlib.Sets.mun_listed_repeat (a := (1 : ℤ)) (b := (2 : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_listed_repeat (a := (1 : ℤ)) (b := (2 : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_listed_repeat (a := (1 : ℤ)) (b := (2 : ℤ))) | (have h := (Parley.Items.Stdlib.Sets.mun_listed_repeat (a := (1 : ℤ)) (b := (2 : ℤ))); ext x; rw [Set.ext_iff] at h; specialize h x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢; tauto) | (have h := (Parley.Items.Stdlib.Sets.mun_listed_repeat (a := (1 : ℤ)) (b := (2 : ℤ))); parley_set_side)
  -- 2. arithmetic
  have s2 : (1 : ℤ) ≠ 2 := by parley_arith
  -- 3. mun:card-pair-distinct u := 1, w := 2, from 2
  have s3 : ({(1 : ℤ), (2 : ℤ)} : Set ℤ).encard = ((2 : ℕ) : ℕ∞) := by first | linear_combination (norm := parley_norm) ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := (1 : ℤ)) (w := (2 : ℤ)))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := (1 : ℤ)) (w := (2 : ℤ)))).mp (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := (1 : ℤ)) (w := (2 : ℤ)))).mp (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := (1 : ℤ)) (w := (2 : ℤ)))).mp (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := (1 : ℤ)) (w := (2 : ℤ)))).mp (by parley_set_side) | exact_mod_cast (((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := (1 : ℤ)) (w := (2 : ℤ)))).mp (by parley_set_side)).symm | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := (1 : ℤ)) (w := (2 : ℤ)))).mp (by parley_set_side); rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := (1 : ℤ)) (w := (2 : ℤ)))).mp (by parley_set_side); qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := (1 : ℤ)) (w := (2 : ℤ)))).mp (by parley_set_side); parley_int_power h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := (1 : ℤ)) (w := (2 : ℤ)))).mp (by parley_set_side); parley_set_side)
  -- 4. substitute {1, 2} = {1, 2, 2} (line 1) into line 3
  have s4 : ({(1 : ℤ), (2 : ℤ), (2 : ℤ)} : Set ℤ).encard = ((2 : ℕ) : ℕ∞) := by parley_subst_at s1 s3
  all_goals exact s4

end Parley.Tests.Notations.Sets.ARepeatCountsOnce

module

public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/an-intersection-counted.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIntersectionCounted.AnIntersectionCounted

theorem an_intersection_counted {α : Type*} (A : Set α) (B : Set α) (D : Set α) (m : ℤ) (hH4 : 0 ≤ m) (n : ℤ) (hH5 : 0 ≤ n) (hH6 : (A ∩ B).encard = ((m.toNat : ℕ) : ℕ∞)) (hH7 : D.encard = ((n.toNat : ℕ) : ℕ∞)) (hH8 : (A ∩ B) ∩ D = ∅) :
    (A ∩ B ∪ D).encard = (((m + n).toNat : ℕ) : ℕ∞) := by
  -- 1. mun:card-disjoint-union X := A ∩ B, Y := D, from H6, H7, H8
  have s1 : (A ∩ B ∪ D).encard = (((m + n).toNat : ℕ) : ℕ∞) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH6 hH7 hH8) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH6 hH7 hH8); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH6 hH7 hH8); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH6 hH7 hH8)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH6 hH7 hH8) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH6 hH7 hH8)).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH6 hH7 hH8); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH6 hH7 hH8); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH6 hH7 hH8); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH6 hH7 hH8); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.AnIntersectionCounted.AnIntersectionCounted

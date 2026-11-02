module

public import LeanBridges
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/an-intersection-counted.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIntersectionCounted.AnIntersectionCounted

theorem an_intersection_counted {α : Type*} (A : Set α) (B : Set α) (D : Set α) (m : ℕ) (n : ℕ) (hH6 : (A ∩ B).encard = ((m : ℕ) : ℕ∞)) (hH7 : D.encard = ((n : ℕ) : ℕ∞)) (hH8 : (A ∩ B) ∩ D = ∅) :
    (A ∩ B ∪ D).encard = ((m + n : ℕ) : ℕ∞) := by
  -- 1. mun:card-disjoint-union X := A ∩ B, Y := D, from H6, H7, H8
  have s1 : (A ∩ B ∪ D).encard = ((m + n : ℕ) : ℕ∞) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (n := n) (by parley_side) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (n := n) (by parley_side) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (n := n) (by parley_side) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (n := n) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (n := n) (by parley_side) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := D) (m := m) (n := n) (by parley_side) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.AnIntersectionCounted.AnIntersectionCounted

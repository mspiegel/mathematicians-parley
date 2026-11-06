module

public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.LastPlace

theorem last_place (m : ℤ) (hH1 : 0 ≤ m) (n : ℤ) (hH2 : 0 ≤ n) (c : Set ℤ) (hH3 : c ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (hH4 : c.encard = ((m.toNat : ℕ) : ℕ∞)) :
    ((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).encard = ((n.toNat : ℕ) : ℕ∞) ∧ ((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).encard = ((m.toNat : ℕ) : ℕ∞) := by
  -- 1. mun:range-finite a := 1, b := m + n
  have s1 : (Set.Icc (1 : ℤ) (m + n) : Set ℤ).Finite := by first | exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := m + n)) | exact ((Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := m + n))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := m + n)) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := m + n)) | (have h := (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := m + n)); parley_set_side)
  -- 2. mun:card-difference X := {1, …, m + n}, Y := c, from H3, 1
  have s2 : (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).ncard : ℤ) = ((Set.Icc (1 : ℤ) (m + n) : Set ℤ).ncard : ℤ) - (c.ncard : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side))) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  -- 3. mun:range-size n := m + n
  have s3 : (Set.Icc (1 : ℤ) (m + n) : Set ℤ).encard = (((m + n).toNat : ℕ) : ℕ∞) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (by parley_set_side))) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (by parley_set_side)); parley_set_side)
  -- 4. algebra, from H4, 2, 3
  have s4 : ((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).encard = ((n.toNat : ℕ) : ℕ∞) := by parley_count_int; (linear_combination (norm := parley_norm) (-1) * hH4 + s2 + s3)
  -- 5. mun:intersection-of-part X := {1, …, m + n}, Y := c, from H3
  have s5 : (Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c = c := by first | exact (Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (by parley_whole_side)); parley_set_side)
  -- 6. calculation
  have s6 : ((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).encard = ((m.toNat : ℕ) : ℕ∞) := by parley_count_after (by
    calc (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).ncard : ℤ) = (c.ncard : ℤ) := by parley_subst s5
      _ = m := by first | parley_set_side | parley_line_toNat hH4)
  -- 7. join 4, 6
  have s7a : ((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).encard = ((n.toNat : ℕ) : ℕ∞) := by parley_set_side
  have s7b : ((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).encard = ((m.toNat : ℕ) : ℕ∞) := by parley_set_side
  exact ⟨by parley_set_side, by parley_set_side⟩

end Parley.Proofs.Wiedijk.Ballot.LastPlace

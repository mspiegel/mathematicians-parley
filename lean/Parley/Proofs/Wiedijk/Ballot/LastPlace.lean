module

public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.LastPlace

theorem last_place (m : ℕ) (n : ℕ) (c : Set ℤ) (hH3 : c ⊆ (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (hH4 : (c.ncard : ℤ) = (m : ℤ)) :
    (((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) \ c).ncard : ℤ) = (n : ℤ) ∧ (((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) ∩ c).ncard : ℤ) = (m : ℤ) := by
  -- 1. mun:range-finite a := 1, b := m + n
  have s1 : (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ).Finite := by first | exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ))) | exact ((Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ))); parley_set_side)
  -- 2. mun:card-difference X := {1, …, m + n}, Y := c, from H3, 1
  have s2 : (((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) \ c).ncard : ℤ) = ((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ).ncard : ℤ) - (c.ncard : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  -- 3. mun:range-size n := m + n
  have s3 : ((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ).ncard : ℤ) = (m : ℤ) + (n : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n)) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_range_size (n := m + n))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n)); parley_set_side)
  -- 4. algebra, from H4, 2, 3
  have s4 : (((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) \ c).ncard : ℤ) = (n : ℤ) := by linear_combination (norm := parley_norm) (-1) * hH4 + s2 + s3
  -- 5. mun:intersection-of-part X := {1, …, m + n}, Y := c, from H3
  have s5 : (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) ∩ c = c := by first | exact (Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (Y := c) (by parley_whole_side)); parley_set_side)
  -- 6. calculation
  have s6 : (((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) ∩ c).ncard : ℤ) = (m : ℤ) := by
    calc (((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) ∩ c).ncard : ℤ) = (c.ncard : ℤ) := by parley_subst s5
      _ = (m : ℤ) := by parley_set_side
  -- 7. join 4, 6
  have s7a : (((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) \ c).ncard : ℤ) = (n : ℤ) := by parley_set_side
  have s7b : (((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) ∩ c).ncard : ℤ) = (m : ℤ) := by parley_set_side
  exact ⟨by parley_set_side, by parley_set_side⟩

end Parley.Proofs.Wiedijk.Ballot.LastPlace

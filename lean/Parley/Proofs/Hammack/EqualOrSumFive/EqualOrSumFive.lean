module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/equal-or-sum-five.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.EqualOrSumFive.EqualOrSumFive

theorem equal_or_sum_five (x : ℝ) (y : ℝ) (hH3 : x ^ 2 + 5 * y = y ^ 2 + 5 * x) :
    (x = y ∨ x + y = 5) := by
  -- 1. axi:excluded-middle P := x + y = 5
  have s1 : x + y = 5 ∨ x + y ≠ 5 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := x + y = 5)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := x + y = 5))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := x + y = 5)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := x + y = 5)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := x + y = 5)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := x + y = 5)); parley_side)
  -- 2. cases, from 1
  have s2 : x = y ∨ x + y = 5 := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. mun:or-right P := x = y, Q := x + y = 5, from C1
      have s2_1 : x = y ∨ x + y = 5 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = y) (Q := x + y = 5) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = y) (Q := x + y = 5) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = y) (Q := x + y = 5) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = y) (Q := x + y = 5) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = y) (Q := x + y = 5) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = y) (Q := x + y = 5) (by parley_side)); parley_side)
      all_goals parley_side
    · skip
      -- 2.2. inequalities, from C2
      have s2_2 : x + y - 5 ≠ 0 := by parley_side
      -- 2.3. algebra, from H3
      have s2_3 : (x - y) * (x + y - 5) = 0 * (x + y - 5) := by linear_combination (norm := parley_norm) hH3
      -- 2.4. mun:multiply-cancel a := x − y, b := 0, c := x + y − 5, from 2.2, 2.3
      have s2_4 : x - y = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x - y) (b := (0 : ℝ)) (c := x + y - 5) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x - y) (b := (0 : ℝ)) (c := x + y - 5) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x - y) (b := (0 : ℝ)) (c := x + y - 5) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x - y) (b := (0 : ℝ)) (c := x + y - 5) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x - y) (b := (0 : ℝ)) (c := x + y - 5) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x - y) (b := (0 : ℝ)) (c := x + y - 5) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x - y) (b := (0 : ℝ)) (c := x + y - 5) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x - y) (b := (0 : ℝ)) (c := x + y - 5) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x - y) (b := (0 : ℝ)) (c := x + y - 5) (by parley_side) (by parley_side)); parley_side)
      -- 2.5. algebra, from 2.4
      have s2_5 : x = y := by linear_combination (norm := parley_norm) s2_4
      -- 2.6. mun:or-left P := x = y, Q := x + y = 5, from 2.5
      have s2_6 : x = y ∨ x + y = 5 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = y) (Q := x + y = 5) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = y) (Q := x + y = 5) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = y) (Q := x + y = 5) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = y) (Q := x + y = 5) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = y) (Q := x + y = 5) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = y) (Q := x + y = 5) (by parley_side)); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.EqualOrSumFive.EqualOrSumFive

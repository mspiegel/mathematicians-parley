module

public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-telescoping-sum-read-upward.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATelescopingSumReadUpward.ATelescopingSumReadUpward

theorem a_telescoping_sum_read_upward (m : ℕ) :
    (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), ((n + 1) ^ 2 - n ^ 2 : ℤ)) = ((m : ℤ) + 1) ^ 2 - 0 ^ 2 := by
  -- 1. thm:sum-telescopes-up a := 0, b := m
  have r9_1 : (m : ℤ) + 1 ≥ 0 := by parley_order
  have s1 : (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), ((n + 1) ^ 2 - n ^ 2 : ℤ)) = ((m : ℤ) + 1) ^ 2 - 0 ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ATelescopingSumReadUpward.ATelescopingSumReadUpward

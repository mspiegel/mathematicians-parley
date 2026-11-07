module

public import NormTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-telescoping-sum-read-upward.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATelescopingSumReadUpward.ATelescopingSumReadUpward

theorem a_telescoping_sum_read_upward (m : ℤ) (hH1 : 0 ≤ m) :
    (∑ n ∈ Finset.Icc (0 : ℤ) m, ((n + 1) ^ 2 - n ^ 2 : ℤ)) = (m + 1) ^ 2 - 0 ^ 2 := by
  -- 1. thm:sum-telescopes-up a := 0, b := m
  have r9_1 : m + 1 ≥ 0 := by parley_order
  have s1 : (∑ n ∈ Finset.Icc (0 : ℤ) m, ((n + 1) ^ 2 - n ^ 2 : ℤ)) = (m + 1) ^ 2 - 0 ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := m) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := m) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := m) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => n ^ 2)) (a := (0 : ℤ)) (b := m) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ATelescopingSumReadUpward.ATelescopingSumReadUpward

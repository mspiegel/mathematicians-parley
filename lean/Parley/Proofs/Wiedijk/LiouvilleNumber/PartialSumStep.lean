module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.LiouvilleNumber.TermsReal

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep

theorem partial_sum_step (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + 1) := by
  -- 1. thm:terms-real m := n + 1
  -- 2. mun:sum-extended a := 1, from 1
  have r218_1 : n ≥ 1 := by parley_order
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)) (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)) (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)) (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)) (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)) (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)) (n := n) (by parley_side)); parley_side)
  -- 3. algebra, from D0, 2
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + 1) := by linear_combination (norm := parley_field) s2
  all_goals exact s3

end Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep

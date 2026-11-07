module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
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
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
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
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumReal
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease

theorem partial_sums_increase (n : ℤ) (hH1 : 0 < n) :
    (∀ j : ℤ, 0 ≤ j → (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) := by
  -- 1. thm:partial-sum-real m := n
  -- 2. induction on j starting at 0
  have s2 : ∀ j : ℤ, 0 ≤ j → (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 2.1. inequalities
      have s2_1 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by parley_order
      all_goals parley_side
    | succ j hK hIH =>
      -- 2.2. mun:nat-plus-nat0 a := n, b := j
      have s2_2 : 0 < n + j := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := n) (by parley_side) (b := j) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := n) (by parley_side) (b := j) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := n) (by parley_side) (b := j) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := n) (by parley_side) (b := j) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := n) (by parley_side) (b := j) (by parley_side)); parley_side)
      -- 2.3. mun:power-positive a := 2, m := (n + j + 1)!
      have r247_1 : (2 : ℤ) > 0 := by parley_arith
      have s2_3 : (2 ^ LeanBridges.Counting.factorial (n + j + 1) : ℤ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side)); parley_side)
      -- 2.4. mun:reciprocal-positive x := 2^((n + j + 1)!), from 2.3
      have s2_4 : (1 / 2 ^ LeanBridges.Counting.factorial (n + j + 1) : ℚ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ LeanBridges.Counting.factorial (n + j + 1) : ℚ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ LeanBridges.Counting.factorial (n + j + 1) : ℚ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ LeanBridges.Counting.factorial (n + j + 1) : ℚ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ LeanBridges.Counting.factorial (n + j + 1) : ℚ)) (by parley_side)); parley_side)
      -- 2.5. thm:partial-sum-real m := n + j, from 2.2
      -- 2.6. inequalities
      have s2_6 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + j + 1) := by parley_order
      -- 2.7. algebra
      have s2_7 : n + j + 1 = n + (j + 1) := by parley_ring
      -- 2.8. calculation
      have s2_8 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n + (j + 1)), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by
        calc (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by parley_side
          _ ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + j + 1) := by parley_side
          _ = (∑ k ∈ Finset.Icc (1 : ℤ) (n + j + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n + j) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n + j) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n + j) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n + j) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n + j) (by parley_side))).symm | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n + j) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n + j) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n + j) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n + j) (by parley_side)); parley_side)
          _ = (∑ k ∈ Finset.Icc (1 : ℤ) (n + (j + 1)), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by
              have s2_7_w : (n : ℚ) + (j : ℚ) + 1 = (n : ℚ) + ((j : ℚ) + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_7; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_7_w | parley_subst s2_7
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease

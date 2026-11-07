module

public import ArithTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Binomial.Binomial

/-! Written from proofs/hammack/binomial-sum-with-powers-of-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialSumWithPowersOfTwo.BinomialSumWithPowersOfTwo

theorem binomial_sum_with_powers_of_two (n : ℤ) (hH1 : 0 ≤ n) :
    (∑ k ∈ Finset.Icc (0 : ℤ) n, (2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℤ) : ℤ)) = 3 ^ n.toNat := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. membership
  -- 3. proof
  have s3 : ∀ k : ℤ, k ∈ Finset.Icc 0 n → (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat = 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ) := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 3.1. mun:one-power m := n − k
    have s3_1 : (1 ^ (n - k) : ℚ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_one_power (m := n - k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := n - k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := n - k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_one_power (m := n - k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_one_power (m := n - k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := n - k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := n - k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := n - k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := n - k)); parley_side)
    -- 3.2. algebra, from 3.1
    have s3_2 : (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat = 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ) := by linear_combination (norm := parley_norm) (2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ)) * s3_1
    all_goals exact s3_2
  -- 4. arithmetic
  have s4 : (1 + 2 : ℤ) = 3 := by parley_arith
  -- 5. calculation
  have s5 : (∑ k ∈ Finset.Icc (0 : ℤ) n, (2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℤ) : ℤ)) = 3 ^ n.toNat := by
    try qify
    calc (∑ k ∈ Finset.Icc (0 : ℤ) n, (2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ) : ℚ)) = (∑ k ∈ Finset.Icc (0 : ℤ) n, ((LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side)); parley_side)
      _ = (1 + 2) ^ n.toNat := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side))).symm | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) (by parley_side)); parley_side)
      _ = 3 ^ n.toNat := by
          have s4_w : (1 + 2 : ℚ) = 3 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s4; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s4_w | parley_subst s4
  all_goals exact s5

end Parley.Proofs.Hammack.BinomialSumWithPowersOfTwo.BinomialSumWithPowersOfTwo

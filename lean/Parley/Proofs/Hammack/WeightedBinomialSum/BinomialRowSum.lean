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

/-! Written from proofs/hammack/weighted-binomial-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.WeightedBinomialSum.BinomialRowSum

theorem binomial_row_sum (m : ℤ) (hH1 : 0 ≤ m) :
    (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℤ) : ℤ)) = 2 ^ m.toNat := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. proof
  have s2 : ∀ k : ℤ, k ∈ Finset.Icc 0 m → (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat = (LeanBridges.Counting.choose m k : ℚ) := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 2.1. mun:one-power m := m − k
    have s2_1 : (1 ^ (m - k) : ℚ) = 1 := by exact (Parley.Items.Stdlib.Numbers.mun_one_power (m := m - k))
    -- 2.2. mun:one-power m := k
    have s2_2 : (1 ^ k.toNat : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_one_power (m := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); parley_side)
    -- 2.3. calculation
    have s2_3 : (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat = (LeanBridges.Counting.choose m k : ℚ) := by
      calc (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat = (LeanBridges.Counting.choose m k : ℚ) * 1 ^ k.toNat := by parley_subst s2_1
        _ = (LeanBridges.Counting.choose m k : ℚ) := by
            have s2_2_w : (1 ^ k.toNat : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_2; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst s2_2_w | parley_subst s2_2
    all_goals exact s2_3
  -- 3. arithmetic
  have s3 : (1 + 1 : ℤ) = 2 := by parley_arith
  -- 4. calculation
  have s4 : (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℤ) : ℤ)) = 2 ^ m.toNat := by
    try qify
    calc (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℚ) : ℚ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat)) (a := (0 : ℤ)) (b := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat)) (a := (0 : ℤ)) (b := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat)) (a := (0 : ℤ)) (b := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat)) (a := (0 : ℤ)) (b := m) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat)) (a := (0 : ℤ)) (b := m) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat)) (a := (0 : ℤ)) (b := m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat)) (a := (0 : ℤ)) (b := m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat)) (a := (0 : ℤ)) (b := m) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat)) (a := (0 : ℤ)) (b := m) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat)) (a := (0 : ℤ)) (b := m) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℚ) * 1 ^ (m - k) * 1 ^ k.toNat)) (a := (0 : ℤ)) (b := m) (by parley_side)); parley_side)
      _ = (1 + 1) ^ m.toNat := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side))).symm | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m) (by parley_side)); parley_side)
      _ = 2 ^ m.toNat := by
          have s3_w : (1 + 1 : ℚ) = 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s3; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s3_w | parley_subst s3
  all_goals exact s4

end Parley.Proofs.Hammack.WeightedBinomialSum.BinomialRowSum

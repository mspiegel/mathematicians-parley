module

public import ArithTactics
public import Counting
public import FactorialTactics
public import InstanceTactics
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

/-! Written from proofs/setmm/binomial-coefficients-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialCoefficientsSum.BinomialCoefficientsSum

theorem binomial_coefficients_sum (N : ℤ) (hH1 : 0 ≤ N) :
    2 ^ N.toNat = (∑ k ∈ Finset.Icc (0 : ℤ) N, ((LeanBridges.Counting.choose N k : ℤ) : ℤ)) := by
  -- 1. proof
  have s1 : ∀ k : ℤ, k ∈ Finset.Icc 0 N → (LeanBridges.Counting.choose N k : ℚ) * 1 ^ (N - k) * 1 ^ k.toNat = (LeanBridges.Counting.choose N k : ℚ) := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 1.1. mun:one-power m := N − k
    have s1_1 : (1 ^ (N - k) : ℚ) = 1 := by exact (Parley.Items.Stdlib.Numbers.mun_one_power (m := N - k))
    -- 1.2. mun:one-power m := k
    have s1_2 : (1 ^ k.toNat : ℤ) = 1 := by
      have hI : (1 ^ k.toNat : ℤ) = 1 := by parley_instance_cast ((Parley.Items.Stdlib.Numbers.mun_one_power (m := k)))
      exact hI
    -- 1.3. calculation
    calc (LeanBridges.Counting.choose N k : ℚ) * 1 ^ (N - k) * 1 ^ k.toNat = (LeanBridges.Counting.choose N k : ℚ) * 1 ^ k.toNat := by linear_combination (norm := parley_norm) (1 ^ k.toNat * (LeanBridges.Counting.choose N k : ℚ)) * s1_1
      _ = (LeanBridges.Counting.choose N k : ℚ) := by
          have s1_2_w : (1 ^ k.toNat : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1_2; push_cast at h; linear_combination (norm := parley_norm) h
          linear_combination (norm := parley_norm) ((LeanBridges.Counting.choose N k : ℤ)) * s1_2_w
  -- 2. arithmetic
  have s2 : (1 + 1 : ℤ) = 2 := by parley_arith
  -- 3. calculation
  try qify
  calc (2 ^ N.toNat : ℚ) = (1 + 1) ^ N.toNat := by
        have s2_w : (1 + 1 : ℚ) = 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2; push_cast at h; linear_combination (norm := parley_norm) h
        first | parley_subst s2_w | parley_subst s2
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) N, ((LeanBridges.Counting.choose N k : ℚ) * 1 ^ (N - k) * 1 ^ k.toNat : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side))).symm | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N) (by parley_side)); parley_side)
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) N, ((LeanBridges.Counting.choose N k : ℚ) : ℚ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose N k : ℚ) * 1 ^ (N - k) * 1 ^ k.toNat)) (u := (fun k : ℤ => (LeanBridges.Counting.choose N k : ℚ))) (a := (0 : ℤ)) (b := N) s1)

end Parley.Proofs.Setmm.BinomialCoefficientsSum.BinomialCoefficientsSum

module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import NormTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
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
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Binomial.BinomialStep

/-! Written from proofs/wiedijk/binomial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Binomial.Binomial

theorem binomial (x : ℝ) (y : ℝ) (n : ℤ) (hH3 : 0 ≤ n) :
    (x + y) ^ n.toNat = (∑ k ∈ Finset.Icc (0 : ℤ) n, ((LeanBridges.Counting.choose n k : ℝ) * x ^ (n - k) * y ^ k.toNat : ℝ)) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → (x + y) ^ m.toNat = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat : ℝ)) := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. mun:binomial-zero-index n := 0
      have s1_1 : (LeanBridges.Counting.choose (0 : ℤ) (0 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_side))
      -- 1.2. calculation
      have s1_2 : (x + y) ^ 0 = (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (0 : ℤ) k : ℝ) * x ^ (0 - k) * y ^ k.toNat : ℝ)) := by
        calc (x + y) ^ 0 = 1 := by parley_ring
          _ = x ^ 0 * y ^ 0 := by parley_ring
          _ = (LeanBridges.Counting.choose (0 : ℤ) (0 : ℤ) : ℝ) * x ^ 0 * y ^ 0 := by
              have s1_1_w : (LeanBridges.Counting.choose (0 : ℤ) (0 : ℤ) : ℝ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s1_1; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s1_1_w | parley_subst s1_1
          _ = (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (0 : ℤ) k : ℝ) * x ^ (0 - k) * y ^ k.toNat : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 : ℤ) k : ℝ) * x ^ (0 - k) * y ^ k.toNat)) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 : ℤ) k : ℝ) * x ^ (0 - k) * y ^ k.toNat)) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 : ℤ) k : ℝ) * x ^ (0 - k) * y ^ k.toNat)) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 : ℤ) k : ℝ) * x ^ (0 - k) * y ^ k.toNat)) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 : ℤ) k : ℝ) * x ^ (0 - k) * y ^ k.toNat)) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 : ℤ) k : ℝ) * x ^ (0 - k) * y ^ k.toNat)) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 : ℤ) k : ℝ) * x ^ (0 - k) * y ^ k.toNat)) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 : ℤ) k : ℝ) * x ^ (0 - k) * y ^ k.toNat)) (a := (0 : ℤ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 : ℤ) k : ℝ) * x ^ (0 - k) * y ^ k.toNat)) (a := (0 : ℤ))); parley_side)
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s1_2
    | succ m hK hIH =>
      -- 1.3. calculation
      calc (x + y) ^ (m + 1).toNat = (x + y) ^ m.toNat * (x + y) := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x + y) (m := m) (by parley_side))
        _ = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat : ℝ)) * (x + y) := by (have h := congrArg (fun t : ℝ => t * (x + y)) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1) k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by exact (Parley.Proofs.Wiedijk.Binomial.BinomialStep.binomial_step (x := x) (y := y) (m := m) (by parley_side))
  -- 2. instantiate m := n in line 1
  exact (s1 n (by parley_side))

end Parley.Proofs.Wiedijk.Binomial.Binomial

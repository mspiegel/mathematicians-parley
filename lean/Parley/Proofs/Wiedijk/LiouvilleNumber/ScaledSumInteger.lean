module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import NormTactics
public import SubstTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Basic.Real.Basic
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
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumReal
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep
public import Parley.Proofs.Wiedijk.LiouvilleNumber.TermsReal

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.ScaledSumInteger

set_option maxHeartbeats 400000 in
theorem scaled_sum_integer :
    (∀ n : ℤ, 0 < n → (∃ m : ℤ, (m : ℚ) = 2 ^ LeanBridges.Counting.factorial n * (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)))) := by
  -- the theorem. induction on n starting at 1
  intro n h_n
  replace h_n : 1 ≤ n := by omega
  induction n, h_n using LeanBridges.Functions.le_induction with
  | base =>
    -- 1. thm:terms-real m := 1
    -- 2. mun:sum-single a := 1, from 1
    have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = 1 / 2 ^ LeanBridges.Counting.factorial (1 : ℤ) := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)))
    -- 3. algebra, from D0, 2
    have s3 : 2 ^ LeanBridges.Counting.factorial (1 : ℤ) * (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = 1 := by linear_combination (norm := parley_field) (2 ^ LeanBridges.Counting.factorial (1 : ℤ)) * s2
    -- 4. membership, from 3
    exact ⟨(1 : ℤ), by first | (push_cast; linarith [s3]) | (rw [s3]; push_cast; ring) | (rw [← s3]; push_cast; ring) | exact s3 | exact s3.symm⟩
  | succ n hK hIH =>
    -- 5. thm:partial-sum-step
    have s5 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + 1) := by exact (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n) (by parley_side))
    -- 6. def:factorial
    have s6 : (LeanBridges.Counting.factorial (n + 1) : ℤ) = (LeanBridges.Counting.factorial n : ℤ) * (n + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) (by parley_side))
    -- 7. calculation
    have s7 : (2 ^ LeanBridges.Counting.factorial (n + 1) : ℤ) = (2 ^ LeanBridges.Counting.factorial n) ^ n.toNat * 2 ^ LeanBridges.Counting.factorial n := by
      calc (2 ^ LeanBridges.Counting.factorial (n + 1) : ℤ) = 2 ^ ((LeanBridges.Counting.factorial n : ℤ) * (n + 1)).toNat := by parley_subst s6
        _ = (2 ^ LeanBridges.Counting.factorial n) ^ (n + 1).toNat := by simpa using (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := (2 : ℤ)) (m := (LeanBridges.Counting.factorial n : ℤ)) (by parley_side) (n := n + 1) (by parley_side))
        _ = (2 ^ LeanBridges.Counting.factorial n) ^ n.toNat * 2 ^ LeanBridges.Counting.factorial n := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 ^ LeanBridges.Counting.factorial n : ℤ)) (m := n) (by parley_side))
    -- 8. algebra, from 5
    have s8 : 2 ^ LeanBridges.Counting.factorial (n + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = 2 ^ LeanBridges.Counting.factorial (n + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 := by linear_combination (norm := parley_field) (2 ^ LeanBridges.Counting.factorial (n + 1)) * s5
    -- 9. substitute
    have s9 : 2 ^ LeanBridges.Counting.factorial (n + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (2 ^ LeanBridges.Counting.factorial n) ^ n.toNat * (2 ^ LeanBridges.Counting.factorial n * (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) + 1 := by
      have c1 : 2 ^ LeanBridges.Counting.factorial (n + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (2 ^ LeanBridges.Counting.factorial n) ^ n.toNat * (2 ^ LeanBridges.Counting.factorial n * (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) := by
        have s7_w : (2 ^ LeanBridges.Counting.factorial (n + 1) : ℚ) = (2 ^ LeanBridges.Counting.factorial n) ^ n.toNat * 2 ^ LeanBridges.Counting.factorial n := by have h := congrArg (fun x : ℤ => (x : ℚ)) s7; push_cast at h; linear_combination (norm := parley_norm) h
        linear_combination (norm := parley_norm) ((∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) * s7_w
      have row1 : 2 ^ LeanBridges.Counting.factorial (n + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (2 ^ LeanBridges.Counting.factorial n) ^ n.toNat * (2 ^ LeanBridges.Counting.factorial n * (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) + 1 := by parley_subst_at c1 s8
      exact row1
    -- 10. membership, from IH
    have s10 : ∃ m : ℤ, (m : ℚ) = (2 ^ LeanBridges.Counting.factorial n) ^ n.toNat * (2 ^ LeanBridges.Counting.factorial n * (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) + 1 := by
      have whole1 : ∃ m : ℤ, (m : ℚ) = 2 ^ LeanBridges.Counting.factorial n * (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by obtain ⟨m, hm⟩ := hIH; exact ⟨m, by first | exact_mod_cast hm | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h)⟩
      exact ⟨((2 ^ LeanBridges.Counting.factorial n) ^ n.toNat * (Classical.choose whole1 : ℤ) + 1), by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring)⟩
    -- 11. substitute (2^(n!))^n·(2^(n!)·s(n)) + 1 = 2^((n + 1)!)·s(n + 1) (line 9) into line 10
    parley_subst_at s9 s10

end Parley.Proofs.Wiedijk.LiouvilleNumber.ScaledSumInteger

module

public import ArithTactics
public import Functions
public import NormTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
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
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Harmonic.HarmonicBlock

/-! Written from proofs/wiedijk/harmonic.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Harmonic.HarmonicUnbounded

set_option maxHeartbeats 400000 in
theorem harmonic_unbounded (M : ℝ) :
    (∃ n : ℤ, 0 < n ∧ (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / (k : ℝ) : ℝ)) > M) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. induction on m starting at 0
  have s2 : ∀ m : ℤ, 0 ≤ m → (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ m.toNat : ℤ), (1 / (k : ℚ) : ℚ)) ≥ (m : ℚ) / 2 := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 2.1. arithmetic
      have s2_1 : (2 ^ 0 : ℤ) = 1 := by parley_arith
      -- 2.2. calculation
      have s2_2 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ 0 : ℤ), (1 / (k : ℚ) : ℚ)) = 1 := by
        calc (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ 0 : ℤ), (1 / (k : ℚ) : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / (k : ℚ) : ℚ)) := by (have h := congrArg (fun t : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) t, (1 / (k : ℚ) : ℚ)) s2_1; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ))); parley_side)
      -- 2.3. arithmetic
      have s2_3 : (1 : ℚ) ≥ 0 / 2 := by parley_arith
      -- 2.4. transitivity, from 2.2, 2.3
      have s2_4 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ 0 : ℤ), (1 / (k : ℚ) : ℚ)) ≥ 0 / 2 := by parley_order
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s2_4
    | succ m hK hIH =>
      -- 2.5. thm:harmonic-block j := m
      have s2_5 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ (m + 1).toNat : ℤ), (1 / (k : ℚ) : ℚ)) ≥ (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ m.toNat : ℤ), (1 / (k : ℚ) : ℚ)) + 1 / 2 := by exact (Parley.Proofs.Wiedijk.Harmonic.HarmonicBlock.harmonic_block (j := m) (by parley_side))
      -- 2.6. inequalities
      have s2_6 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ m.toNat : ℤ), (1 / (k : ℚ) : ℚ)) + 1 / 2 ≥ ((m : ℚ) + 1) / 2 := by parley_order
      -- 2.7. transitivity, from 2.5, 2.6
      have s2_7 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ (m + 1).toNat : ℤ), (1 / (k : ℚ) : ℚ)) ≥ ((m : ℚ) + 1) / 2 := by parley_order
      (have h := s2_7; push_cast at h ⊢; all_goals exact h)
  -- 3. obtain N: thm:archimedean-natural x := 2M
  obtain ⟨N, s3a, s3b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean_natural (x := 2 * M))
  -- 4. instantiate m := N in line 2
  have s4 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ N.toNat : ℤ), (1 / (k : ℚ) : ℚ)) ≥ (N : ℚ) / 2 := by exact (s2 N (by parley_side))
  -- 5. inequalities
  have s5 : (N : ℝ) / 2 > M := by parley_order
  -- 6. transitivity, from 4, 5
  have s6 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ N.toNat : ℤ), (1 / (k : ℝ) : ℝ)) > M := by parley_order
  -- 7. exhibit, from 6
  exact ⟨(2 ^ N.toNat : ℤ), by parley_side, s6⟩

end Parley.Proofs.Wiedijk.Harmonic.HarmonicUnbounded

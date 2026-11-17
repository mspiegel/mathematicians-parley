module

public import Counting
public import Polynomials
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Polynomials
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Liouville.Liouville
public import Parley.Proofs.Wiedijk.LiouvilleNumber.LaterAtLeast
public import Parley.Proofs.Wiedijk.LiouvilleNumber.LaterAtMost
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumReal
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease
public import Parley.Proofs.Wiedijk.LiouvilleNumber.ScaledSumInteger
public import Parley.Proofs.Wiedijk.LiouvilleNumber.TermsReal

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.LiouvilleNumber

theorem liouville_number :
    Transcendental ℤ ((Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) : ℝ) : ℂ) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. proof
  have s2 : ∀ n : ℤ, 0 < n → (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by
    intro n hK2
    -- 2.1. thm:partial-sums-increase
    have s2_1 : ∀ j : ℤ, 0 ≤ j → (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by exact (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease.partial_sums_increase (n := n) hK2)
    -- 2.2. instantiate j := 1 in line 2.1
    exact (s2_1 (1 : ℤ) (by norm_num))
  -- 3. thm:terms-real m := 1
  -- 4. calculation
  have s4 : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = 1 / 2 := by
    calc (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := rfl
      _ = 1 / 2 ^ LeanBridges.Counting.factorial (1 : ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)))
      _ = 1 / 2 := by norm_num
  -- 5. arithmetic
  have s5 : (2 / 2 ^ LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℚ) = 1 / 2 := by norm_num [Nat.factorial]
  -- 6. inequalities, from 4, 5
  have s6 : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 2 / 2 ^ LeanBridges.Counting.factorial (1 + 1 : ℤ) = 1 := by linarith only [s4, s5]
  -- 7. thm:later-at-most n := 1
  have s7 : ∀ i : ℤ, 0 < i → i ≥ 1 → (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 2 / 2 ^ LeanBridges.Counting.factorial (1 + 1 : ℤ) := by exact (Parley.Proofs.Wiedijk.LiouvilleNumber.LaterAtMost.later_at_most (n := (1 : ℤ)) (by norm_num))
  -- 8. proof
  have s8 : ∀ n : ℤ, 0 < n → (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ 1 := by
    intro n hK4
    -- 8.1. calculation
    calc (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 2 / 2 ^ LeanBridges.Counting.factorial (1 + 1 : ℤ) := by exact (s7 n hK4 hK4)
      _ = 1 := s6
  -- 9. obtain L: thm:monotone-limit x := (n ∈ ℕ ↦ s(n)), B := 1, from 2, 8
  obtain ⟨L, s9_obtained⟩ := (Parley.Items.Stdlib.Calculus.thm_monotone_limit (x := (fun x : ℤ => (((fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) (x : ℤ) : ℚ) : ℝ))) (by intro n h_n; exact by have h := (Rat.cast_le (K := ℝ)).mpr (s2 n h_n); simp only [Rat.cast_sum, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; push_cast at h ⊢; exact h) (B := (1 : ℝ)) (by intro n h_n; exact by have h := (Rat.cast_le (K := ℝ)).mpr (s8 n h_n); simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; push_cast at h ⊢; exact h))
  have s9 : Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ) : ℝ)) Filter.atTop (nhds L) := by (have h := s9_obtained; push_cast at h ⊢; exact h)
  -- 10. contradiction
  have s10 : ¬ IsAlgebraic ℤ (L : ℂ) := by
    intro hS
    -- 10.1. obtain F: thm:algebraic-root α := L, from S
    obtain ⟨F, _, s10_1⟩ := (Parley.Items.Stdlib.Polynomials.thm_algebraic_root (α := (L : ℂ)) hS)
    have hD1_kind : 0 < (LeanBridges.Polynomials.degree F : ℤ) := by exact s10_1.1.2
    set N : ℤ := (LeanBridges.Polynomials.degree F : ℤ) with hD1
    have hD1_pos := hD1_kind
    -- 10.2. obtain c: thm:liouville F := F, α := L, from D1, 10.1
    obtain ⟨c, ⟨s10_2a, s10_2b⟩⟩ := (Parley.Proofs.Wiedijk.Liouville.Liouville.liouville (F := F) s10_1.1.1 (N := (LeanBridges.Polynomials.degree F : ℤ)) hD1_pos rfl (α := L) s10_1.2)
    -- 10.3. obtain m: thm:archimedean-natural x := 2/c
    have r481_1 : c ≠ 0 := ne_of_gt (by linarith only [s10_2a])
    obtain ⟨m, s10_3a, s10_3b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean_natural (x := 2 / c))
    have hD2_kind : 0 < m + N := by
      simp only [hD1] at ⊢
      push_cast at ⊢
      exact (Parley.Items.Stdlib.Numbers.mun_nat_closure_1 (a := m) s10_3a (b := (LeanBridges.Polynomials.degree F : ℤ)) hD1_pos)
    set r : ℤ := m + N with hD2
    have hD2_pos := hD2_kind
    -- 10.4. mun:factorial-nat n := r
    have s10_4 : 0 < (LeanBridges.Counting.factorial r : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := r) (le_of_lt hD2_pos))
    have hD3_kind : (0 : ℤ) < 2 ^ LeanBridges.Counting.factorial r := by exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by norm_num) (m := (LeanBridges.Counting.factorial r : ℤ)) (le_of_lt s10_4))
    set d : ℤ := (2 ^ LeanBridges.Counting.factorial r : ℤ) with hD3
    have hD3_pos := hD3_kind
    -- 10.5. thm:scaled-sum-integer
    have s10_5 : ∀ n : ℤ, 0 < n → (∃ m : ℤ, (m : ℚ) = 2 ^ LeanBridges.Counting.factorial n * (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) := by exact Parley.Proofs.Wiedijk.LiouvilleNumber.ScaledSumInteger.scaled_sum_integer
    -- 10.6. instantiate n := r in line 10.5, from D2
    have s10_6 : ∃ m : ℤ, (m : ℚ) = 2 ^ LeanBridges.Counting.factorial r * (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by exact (s10_5 r hD2_pos)
    -- 10.7. substitute 2^(r!) = d (D3) into line 10.6
    have s10_7 : ∃ m : ℤ, (m : ℚ) = (d : ℚ) * (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by
      have e_w : 2 ^ LeanBridges.Counting.factorial r = (d : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) hD3.symm; push_cast at h; linear_combination h
      exact Eq.subst (motive := (fun t : ℚ => ∃ m : ℤ, (m : ℚ) = t * (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)))) e_w s10_6
    -- 10.8. instantiate p := d·s(r), q := d in line 10.2, from D3, 10.7
    have s10_8 : L = (d : ℝ) * (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) / (d : ℝ) ∨ c / (d : ℝ) ^ N.toNat < abs (L - (d : ℝ) * (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) / (d : ℝ)) := by rw [← (by have h := congrArg (fun x => ((x : ℚ) : ℝ)) (Classical.choose_spec s10_7); push_cast at h; exact h : ((Classical.choose s10_7 : ℤ) : ℝ) = (d : ℝ) * (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)))]; (exact_mod_cast (s10_2b (Classical.choose s10_7) d hD3_pos))
    -- 10.9. substitute
    have s10_9 : L = (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) ∨ c / (d : ℝ) ^ N.toNat < abs (L - (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ))) := by
      have c1 : (d : ℚ) * (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) / (d : ℚ) = (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by field
      have row1 : L = (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) ∨ c / (d : ℝ) ^ N.toNat < abs (L - (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ))) := by
        have e_w : (d : ℝ) * (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) / (d : ℝ) = (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) := by have h := congrArg (fun x : ℚ => (x : ℝ)) c1; push_cast at h ⊢; linear_combination h
        exact Eq.subst (motive := (fun t : ℝ => L = t ∨ c / (d : ℝ) ^ N.toNat < abs (L - t))) e_w s10_8
      exact row1
    -- 10.10. thm:later-at-least n := r, from D2
    have s10_10 : ∀ i : ℤ, 0 < i → i ≥ r + 1 → (∑ k ∈ Finset.Icc (1 : ℤ) (r + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by
      simp only [hD2] at ⊢
      push_cast at ⊢
      exact (Parley.Proofs.Wiedijk.LiouvilleNumber.LaterAtLeast.later_at_least (n := m + N) hD2_pos)
    -- 10.11. thm:partial-sum-step n := r, from D2
    have s10_11 : (∑ k ∈ Finset.Icc (1 : ℤ) (r + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (r + 1) := by
      simp only [hD2] at ⊢
      push_cast at ⊢
      exact (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := m + N) hD2_pos)
    -- 10.12. mun:factorial-nat n := r + 1
    have s10_12 : 0 < (LeanBridges.Counting.factorial (r + 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := r + 1) (add_nonneg (le_of_lt hD2_pos) (by norm_num)))
    have hD4_kind : (0 : ℤ) < 2 ^ LeanBridges.Counting.factorial (r + 1) := by exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by norm_num) (m := (LeanBridges.Counting.factorial (r + 1) : ℤ)) (le_of_lt s10_12))
    set e : ℤ := (2 ^ LeanBridges.Counting.factorial (r + 1) : ℤ) with hD4
    have hD4_pos := hD4_kind
    -- 10.13. substitute 2^((r + 1)!) = e (D4) into line 10.11
    have s10_13 : (∑ k ∈ Finset.Icc (1 : ℤ) (r + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / (e : ℚ) := by
      have e_w : 2 ^ LeanBridges.Counting.factorial (r + 1) = (e : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) hD4.symm; push_cast at h; linear_combination h
      exact Eq.subst (motive := (fun t : ℚ => (∑ k ∈ Finset.Icc (1 : ℤ) (r + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / t)) e_w s10_11
    -- 10.14. mun:reciprocal-positive x := e
    have r530_1 : e > 0 := by linarith only [hD4_pos, hD4]
    have s10_14 : 1 / (e : ℚ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (e : ℚ)) (by exact_mod_cast gt_iff_lt.mp r530_1))
    -- 10.15. inequalities
    have s10_15 : (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) < (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / (e : ℚ) := by linarith only [s10_14]
    -- 10.16. calculation
    have s10_16 : (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) < L := by
      calc (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) < (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) + 1 / (e : ℝ) := (show (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) < (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) + 1 / (e : ℝ) by have h := (Rat.cast_lt (K := ℝ)).mpr s10_15; simp only [Rat.cast_sum, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; exact h)
        _ = (∑ k ∈ Finset.Icc (1 : ℤ) (r + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) := by have h := (Rat.cast_inj (α := ℝ)).mpr s10_13.symm; simp only [Rat.cast_sum, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; push_cast at h ⊢; exact h
        _ ≤ L := by exact (Parley.Items.Stdlib.Calculus.thm_limit_at_least (x := (fun x : ℤ => (((fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) (x : ℤ) : ℚ) : ℝ))) (L := L) (by (have h := s9; push_cast at h ⊢; exact h)) (B := ∑ k ∈ Finset.Icc (1 : ℤ) (r + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) (N := r + 1) (add_pos (hD2_pos) (by norm_num)) (by intro n h_n h_3; exact by have h := (Rat.cast_le (K := ℝ)).mpr (s10_10 n h_n h_3); simp only [Rat.cast_sum, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; push_cast at h ⊢; exact h))
    -- 10.17. inequalities
    have s10_17 : L ≠ (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) := by linarith only [s10_16]
    -- 10.18. thm:later-at-most n := r, from D2
    have s10_18 : ∀ i : ℤ, 0 < i → i ≥ r → (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 2 / 2 ^ LeanBridges.Counting.factorial (r + 1) := by
      simp only [hD2] at ⊢
      push_cast at ⊢
      exact (Parley.Proofs.Wiedijk.LiouvilleNumber.LaterAtMost.later_at_most (n := m + N) hD2_pos)
    -- 10.19. substitute 2^((r + 1)!) = e (D4) into line 10.18
    have s10_19 : ∀ i : ℤ, 0 < i → i ≥ r → (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 2 / (e : ℚ) := by
      have e_w : 2 ^ LeanBridges.Counting.factorial (r + 1) = (e : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) hD4.symm; push_cast at h; linear_combination h
      exact Eq.subst (motive := (fun t : ℚ => ∀ i : ℤ, 0 < i → i ≥ r → (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 2 / t)) e_w s10_18
    -- 10.20. thm:limit-at-most x := (n ∈ ℕ ↦ s(n)), B := s(r) + 2/e, N := r, from 9, 10.19
    have s10_20 : L ≤ (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) + 2 / (e : ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_limit_at_most (x := (fun x : ℤ => (((fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) (x : ℤ) : ℚ) : ℝ))) (L := L) (by (have h := s9; push_cast at h ⊢; exact h)) (B := (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) + 2 / (e : ℝ)) (N := r) hD2_pos (by intro n h_n h_3; exact by have h := (Rat.cast_le (K := ℝ)).mpr (s10_19 n h_n h_3); simp only [Rat.cast_sum, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; push_cast at h ⊢; exact h))
    -- 10.21. mun:quotient-positive x := 2, y := e
    have r567_1 : (2 : ℤ) > 0 := by norm_num
    have r567_2 : e > 0 := by linarith only [hD4_pos, hD4]
    have s10_21 : 2 / (e : ℚ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 : ℚ)) (y := (e : ℚ)) (by norm_num) (by exact_mod_cast gt_iff_lt.mp r567_2))
    -- 10.22. inequalities
    have s10_22 : -(2 / (e : ℚ)) ≤ 0 := by linarith only [s10_21]
    -- 10.23. inequalities
    have s10_23 : (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) ≤ L := by linarith only [s10_16]
    -- 10.24. inequalities, from 10.22, 10.23
    have s10_24 : (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) - 2 / (e : ℝ) ≤ L := by linarith only [(show -(2 / (e : ℝ)) ≤ 0 by have h := (Rat.cast_le (K := ℝ)).mpr s10_22; simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_zero, Rat.cast_ofNat, Rat.cast_intCast] at h; exact h), s10_23]
    -- 10.25. calculation
    have s10_25 : c / (d : ℝ) ^ N.toNat < 2 / (e : ℝ) := by
      calc c / (d : ℝ) ^ N.toNat < abs (L - (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ))) := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := L = (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ))) (Q := c / (d : ℝ) ^ N.toNat < abs (L - (∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)))) s10_9 s10_17)
        _ ≤ 2 / (e : ℝ) := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_le (x := L) (c := ∑ k ∈ Finset.Icc (1 : ℤ) r, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) (δ := 2 / (e : ℝ)))).mpr ⟨s10_24, s10_20⟩
    -- 10.26. mun:nat-closure a := r!, b := N, from D1
    have s10_26 : 0 < (LeanBridges.Counting.factorial r : ℤ) * N := by
      simp only [hD1] at ⊢
      push_cast at ⊢
      exact (Parley.Items.Stdlib.Numbers.mun_nat_closure_2 (a := (LeanBridges.Counting.factorial r : ℤ)) (LeanBridges.Counting.factorial_nat (r) (le_of_lt hD2_pos)) (b := (LeanBridges.Polynomials.degree F : ℤ)) hD1_pos)
    -- 10.27. mun:nat-closure a := r!, b := m + 1
    have s10_27 : 0 < (LeanBridges.Counting.factorial r : ℤ) * (m + 1) := by exact (Parley.Items.Stdlib.Numbers.mun_nat_closure_2 (a := (LeanBridges.Counting.factorial r : ℤ)) (LeanBridges.Counting.factorial_nat (r) (le_of_lt hD2_pos)) (b := m + 1) (add_pos (s10_3a) (by norm_num)))
    have hD5_kind : (0 : ℤ) < 2 ^ ((LeanBridges.Counting.factorial r : ℤ) * N).toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by norm_num) (m := (LeanBridges.Counting.factorial r : ℤ) * N) (le_of_lt s10_26))
    set Q : ℤ := (2 ^ ((LeanBridges.Counting.factorial r : ℤ) * N).toNat : ℤ) with hD5
    have hD5_pos := hD5_kind
    have hD6_kind : (0 : ℤ) < 2 ^ ((LeanBridges.Counting.factorial r : ℤ) * (m + 1)).toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by norm_num) (m := (LeanBridges.Counting.factorial r : ℤ) * (m + 1)) (le_of_lt s10_27))
    set R : ℤ := (2 ^ ((LeanBridges.Counting.factorial r : ℤ) * (m + 1)).toNat : ℤ) with hD6
    have hD6_pos := hD6_kind
    -- 10.28. mun:power-of-power a := 2, m := r!, n := N
    have s10_28 : (2 ^ ((LeanBridges.Counting.factorial r : ℤ) * N).toNat : ℤ) = (2 ^ LeanBridges.Counting.factorial r) ^ N.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := (2 : ℤ)) (m := (LeanBridges.Counting.factorial r : ℤ)) (Nat.cast_nonneg _) (n := N) (le_of_lt hD1_pos))
    -- 10.29. algebra, from D3, D5, 10.28
    have s10_29 : d ^ N.toNat = Q := by
      simp only [hD3, hD5] at ⊢
      push_cast at ⊢
      linear_combination (-1) * s10_28
    -- 10.30. def:factorial n := r
    have s10_30 : (LeanBridges.Counting.factorial (r + 1) : ℤ) = (LeanBridges.Counting.factorial r : ℤ) * (r + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := r) (le_of_lt hD2_pos))
    -- 10.31. algebra, from D2
    have s10_31 : (LeanBridges.Counting.factorial r : ℤ) * (r + 1) = (LeanBridges.Counting.factorial r : ℤ) * N + (LeanBridges.Counting.factorial r : ℤ) * (m + 1) := by
      simp only [hD2] at ⊢
      push_cast at ⊢
      ring1
    -- 10.32. calculation
    have s10_32 : e = Q * R := by
      calc e = 2 ^ LeanBridges.Counting.factorial (r + 1) := by simp (disch := omega) only [hD4]
        _ = 2 ^ ((LeanBridges.Counting.factorial r : ℤ) * (r + 1)).toNat := by
            have e_nat : LeanBridges.Counting.factorial (r + 1) = ((LeanBridges.Counting.factorial r : ℤ) * (r + 1)).toNat := by (have h := s10_30; omega)
            exact congrArg (fun t : ℕ => 2 ^ t) e_nat
        _ = 2 ^ ((LeanBridges.Counting.factorial r : ℤ) * N + (LeanBridges.Counting.factorial r : ℤ) * (m + 1)).toNat := congrArg (fun t : ℤ => 2 ^ t.toNat) s10_31
        _ = 2 ^ ((LeanBridges.Counting.factorial r : ℤ) * N).toNat * 2 ^ ((LeanBridges.Counting.factorial r : ℤ) * (m + 1)).toNat := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (2 : ℤ)) (m := (LeanBridges.Counting.factorial r : ℤ) * N) (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hD1_pos)) (n := (LeanBridges.Counting.factorial r : ℤ) * (m + 1)) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (le_of_lt s10_3a) (by norm_num))))
        _ = Q * R := by simp only [hD5, hD6] at ⊢
    -- 10.33. substitute
    have s10_33 : c / (Q : ℝ) < 2 / ((Q : ℝ) * (R : ℝ)) := by
      have c1 : d ^ N.toNat = Q := congrArg (fun t : ℤ => t) s10_29
      have row1 : c / (Q : ℝ) < 2 / (e : ℝ) := by
        have e_w : (d : ℝ) ^ N.toNat = (Q : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) c1; push_cast at h; linear_combination h
        exact Eq.subst (motive := (fun t : ℝ => c / t < 2 / (e : ℝ))) e_w s10_25
      have c2 : e = Q * R := congrArg (fun t : ℤ => t) s10_32
      have row2 : c / (Q : ℝ) < 2 / ((Q : ℝ) * (R : ℝ)) := by
        have e_w : (e : ℝ) = (Q : ℝ) * (R : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) c2; push_cast at h; linear_combination h
        exact Eq.subst (motive := (fun t : ℝ => c / (Q : ℝ) < 2 / t)) e_w row1
      exact row2
    -- 10.34. mun:product-positive x := Q, y := R
    have r634_1 : Q > 0 := by linarith only [hD5_pos, hD5]
    have r634_2 : R > 0 := by linarith only [hD6_pos, hD6]
    have s10_34 : Q * R > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_positive (x := Q) (y := R) r634_1 r634_2)
    -- 10.35. mun:cross-multiplied-order a := c, b := Q·R, c := 2, d := Q, from 10.33, 10.34
    have r639_1 : Q > 0 := by linarith only [hD5_pos, hD5]
    have s10_35 : c * ((Q : ℝ) * (R : ℝ)) < 2 * (Q : ℝ) := ((Parley.Items.Stdlib.Numbers.mun_cross_multiplied_order (a := c) (b := (Q : ℝ) * (R : ℝ)) (by exact_mod_cast gt_iff_lt.mp s10_34) (c := (2 : ℝ)) (d := (Q : ℝ)) (by exact_mod_cast gt_iff_lt.mp r639_1))).mpr s10_33
    -- 10.36. inequalities
    have s10_36 : (Q : ℝ) * (c * (R : ℝ)) < (Q : ℝ) * 2 := by linarith only [s10_35]
    -- 10.37. mun:less-scaled x := c·R, y := 2, c := Q, from 10.36
    have r648_1 : Q > 0 := by linarith only [hD5_pos, hD5]
    have s10_37 : c * (R : ℝ) < 2 := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := c * (R : ℝ)) (y := (2 : ℝ)) (c := (Q : ℝ)) (by exact_mod_cast gt_iff_lt.mp r648_1))).mpr s10_36
    -- 10.38. inequalities
    have s10_38 : c * (R : ℝ) ≤ 2 := by linarith only [s10_37]
    -- 10.39. inequalities, from 10.4
    have s10_39 : 1 ≤ (LeanBridges.Counting.factorial r : ℤ) := by linarith only [s10_4]
    -- 10.40. mun:multiply-le-nonneg x := 1, y := r!, c := m + 1, from 10.39
    have r660_1 : m + 1 ≥ 0 := by linarith only [s10_3a]
    have s10_40 : 1 * (m + 1) ≤ (LeanBridges.Counting.factorial r : ℤ) * (m + 1) := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := (1 : ℤ)) (y := (LeanBridges.Counting.factorial r : ℤ)) (c := m + 1) s10_39 r660_1)
    -- 10.41. inequalities
    have s10_41 : m + 1 ≤ (LeanBridges.Counting.factorial r : ℤ) * (m + 1) := by linarith only [s10_40]
    -- 10.42. mun:power-exponent-le a := 2, m := m + 1, n := r!·(m + 1), from 10.41
    have r669_1 : (1 : ℤ) ≤ 2 := by norm_num
    have s10_42 : (2 ^ (m + 1).toNat : ℤ) ≤ 2 ^ ((LeanBridges.Counting.factorial r : ℤ) * (m + 1)).toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := (2 : ℤ)) (m := m + 1) (add_nonneg (le_of_lt s10_3a) (by norm_num)) (n := (LeanBridges.Counting.factorial r : ℤ) * (m + 1)) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (le_of_lt s10_3a) (by norm_num))) (by norm_num) s10_41)
    -- 10.43. substitute 2^(r!·(m + 1)) = R (D6) into line 10.42
    have s10_43 : 2 ^ (m + 1).toNat ≤ R := Eq.subst (motive := (fun t : ℤ => 2 ^ (m + 1).toNat ≤ t)) hD6.symm s10_42
    -- 10.44. inequalities
    have s10_44 : m < 1 + 1 * (m + 1) := by linarith
    -- 10.45. calculation
    have r679_1 : (1 : ℤ) ≥ -1 := by norm_num
    have s10_45 : m < R := by
      calc m < 1 + 1 * (m + 1) := s10_44
        _ ≤ (1 + 1) ^ (m + 1).toNat := by exact (Parley.Items.Stdlib.Numbers.thm_bernoulli_inequality (x := (1 : ℤ)) (n := m + 1) (add_nonneg (le_of_lt s10_3a) (by norm_num)) (by norm_num))
        _ = 2 ^ (m + 1).toNat := by norm_num
        _ ≤ R := s10_43
    -- 10.46. transitivity, from 10.3, 10.45
    have r687_1 : c ≠ 0 := ne_of_gt (by linarith only [s10_2a])
    have s10_46 : 2 / c < (R : ℝ) := by exact lt_trans s10_3b (show (m : ℝ) < (R : ℝ) by exact_mod_cast s10_45)
    -- 10.47. calculation
    have r691_1 : c ≠ 0 := ne_of_gt (by linarith only [s10_2a])
    have s10_47 : 2 < c * (R : ℝ) := by
      calc (2 : ℝ) = c * (2 / c) := by have hz1 : c ≠ 0 := r691_1; field
        _ < c * (R : ℝ) := by exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := 2 / c) (y := (R : ℝ)) (c := c) s10_2a)).mp s10_46
    -- 10.48. inequalities, from 10.38
    have s10_48 : ¬ 2 < c * (R : ℝ) := by linarith only [s10_38]
    exact s10_48 s10_47
  -- 11. def:transcendental, from 10
  have s11 : Transcendental ℤ (L : ℂ) := ((Parley.Items.Stdlib.Polynomials.def_transcendental (α := (L : ℂ)))).mpr s10
  -- 12. substitute
  have c1 : L = Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) := by
    have hI : Filter.limUnder Filter.atTop (fun n : ℤ => ∑ a ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial a : ℝ)) = L := by exact ((Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ))) (L := L) s9))
    exact hI.symm
  have row1 : Transcendental ℤ ((Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) : ℝ) : ℂ) := Eq.subst (motive := (fun t : ℝ => Transcendental ℤ (t : ℂ))) c1 s11
  exact row1

end Parley.Proofs.Wiedijk.LiouvilleNumber.LiouvilleNumber

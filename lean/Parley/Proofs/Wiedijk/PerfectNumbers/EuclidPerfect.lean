module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.GeometricSeries.GeometricSum

/-! Written from proofs/wiedijk/perfect-numbers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PerfectNumbers.EuclidPerfect

set_option maxHeartbeats 400000 in
theorem euclid_perfect (p : ℤ) (hH1 : 0 < p) (hH2 : Nat.Prime (2 ^ p.toNat - 1 : ℤ).toNat) :
    (∃ m : ℕ, (m : ℚ) = (2 ^ (p - 1) * (2 ^ p.toNat - 1) : ℚ) ∧ ArithmeticFunction.sigma 1 m = 2 * m) := by
  -- 1. algebra
  have s1 : p - 1 + 1 = p := by parley_ring
  -- 2. mun:exponent-step a := 2, m := p − 1
  have r62_1 : 0 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := p) (by parley_side))
  have s2 : (2 ^ (p - 1 + 1) : ℚ) = 2 ^ (p - 1) * 2 := by (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℚ)) (m := p - 1) (by parley_side)); simp only [parley_zpow_toNat (n := p - 1 + 1) (h := add_nonneg (r62_1) (by norm_num)), parley_zpow_toNat (n := p - 1) (h := r62_1)] at h ⊢; exact_mod_cast h)
  -- 3. substitute (p − 1) + 1 = p (line 1) into line 2
  have s3 : (2 ^ p.toNat : ℚ) = 2 ^ (p - 1) * 2 := by (have h := Eq.subst (motive := (fun t : ℤ => (2 ^ t : ℚ) = 2 ^ (p - 1) * 2)) s1 s2; simp only [parley_zpow_toNat (n := p) (h := le_of_lt hH1)] at h ⊢; exact_mod_cast h)
  -- 4. contradiction
  have s4 : ¬ (∃ m : ℤ, (m : ℚ) = (2 ^ (p - 1) : ℚ) ∧ (2 ^ p.toNat - 1 : ℤ) ∣ m) := by
    intro hS
    -- 4.1. mun:divides-multiple e := 2^p − 1, a := 2^(p − 1), x := 2, from S
    have r73_1 : 0 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := p) (by parley_side))
    have s4_1 : ∃ m : ℤ, (m : ℚ) = (2 ^ (p - 1) * 2 : ℚ) ∧ (2 ^ p.toNat - 1 : ℤ) ∣ m := by
      have whole1 : ((2 : ℚ) : ℚ) ^ (p - 1).toNat = (2 ^ (p - 1) : ℚ) := by rw [← zpow_natCast, Int.toNat_of_nonneg r73_1]
      have hS := parley_witness_at hS (((2 : ℤ) ^ (p - 1).toNat) : ℤ) (by (push_cast; simp only [whole1]; all_goals ring))
      refine ⟨(((2 : ℤ) ^ (p - 1).toNat) * 2 : ℤ), by (push_cast; simp only [whole1]; all_goals ring), ?_⟩
      (exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (2 ^ p.toNat - 1 : ℤ)) (a := (((2 : ℤ) ^ (p - 1).toNat) : ℤ)) (x := (2 : ℤ)) hS))
    -- 4.2. substitute 2^p = 2^(p − 1)·2 (line 3) into line 4.1
    have s4_2 : (2 ^ p.toNat - 1 : ℤ) ∣ (2 ^ p.toNat : ℤ) := by exact parley_witness_at (Eq.subst (motive := (fun t : ℚ => ∃ m : ℤ, (m : ℚ) = t ∧ (2 ^ p.toNat - 1 : ℤ) ∣ m)) s3.symm s4_1) (2 ^ p.toNat : ℤ) (by norm_cast)
    -- 4.3. mun:divides-self n := 2^p − 1
    have s4_3 : (2 ^ p.toNat - 1 : ℤ) ∣ (2 ^ p.toNat - 1 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (2 ^ p.toNat - 1 : ℤ)))
    -- 4.4. mun:divides-difference d := 2^p − 1, a := 2^p, b := 2^p − 1, from 4.2, 4.3
    have s4_4 : (2 ^ p.toNat - 1 : ℤ) ∣ (2 ^ p.toNat - (2 ^ p.toNat - 1) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (2 ^ p.toNat - 1 : ℤ)) (a := (2 ^ p.toNat : ℤ)) (b := (2 ^ p.toNat - 1 : ℤ)) s4_2 s4_3)
    -- 4.5. substitute
    have s4_5 : (2 ^ p.toNat - 1 : ℤ) ∣ (1 : ℤ) := by
      have c1 : (2 ^ p.toNat - (2 ^ p.toNat - 1) : ℤ) = 1 := by parley_ring
      have row1 : (2 ^ p.toNat - 1 : ℤ) ∣ (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (2 ^ p.toNat - 1 : ℤ) ∣ t)) c1 s4_4; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 4.6. mun:divides-one d := 2^p − 1, from 4.5
    have r91_1 : (0 : ℤ) < 2 ^ p.toNat - 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ p.toNat - 1 : ℤ)) hH2)
    have s4_6 : (2 ^ p.toNat - 1 : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (2 ^ p.toNat - 1 : ℤ)) (by parley_side) s4_5)
    -- 4.7. def:prime p := 2^p − 1, from H2
    have r95_1 : (0 : ℤ) < 2 ^ p.toNat - 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ p.toNat - 1 : ℤ)) hH2)
    have s4_7 : (2 ^ p.toNat - 1 : ℤ) > 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ p.toNat - 1 : ℤ)) (by parley_side))).mp hH2).1
    -- 4.8. inequalities
    have s4_8 : (2 ^ p.toNat - 1 : ℤ) ≠ 1 := by parley_side
    exact s4_8 s4_6
  -- 5. calculation
  have r104_1 : (0 : ℤ) < 2 ^ p.toNat - 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ p.toNat - 1 : ℤ)) hH2)
  have r104_2 : 0 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := p) (by parley_side))
  have s5 : ∃ m : ℤ, (m : ℚ) = (2 ^ (p - 1) : ℚ) ∧ (Int.gcd m (2 ^ p.toNat - 1 : ℤ) : ℤ) = 1 := by
    have whole1 : ((2 : ℚ) : ℚ) ^ (p - 1).toNat = (2 ^ (p - 1) : ℚ) := by rw [← zpow_natCast, Int.toNat_of_nonneg r104_2]
    have s4 := parley_witness_not_at s4 (((2 : ℤ) ^ (p - 1).toNat) : ℤ) (by (push_cast; simp only [whole1]; all_goals ring))
    refine ⟨(((2 : ℤ) ^ (p - 1).toNat) : ℤ), by (push_cast; simp only [whole1]; all_goals ring), ?_⟩
    exact (by
      calc (Int.gcd (((2 : ℤ) ^ (p - 1).toNat) : ℤ) (2 ^ p.toNat - 1 : ℤ) : ℤ) = (Int.gcd (2 ^ p.toNat - 1 : ℤ) (((2 : ℤ) ^ (p - 1).toNat) : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (((2 : ℤ) ^ (p - 1).toNat) : ℤ)) (b := (2 ^ p.toNat - 1 : ℤ)))
        _ = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (2 ^ p.toNat - 1 : ℤ)) (by parley_side) hH2 (a := (((2 : ℤ) ^ (p - 1).toNat) : ℤ)) s4))
  -- 6. calculation
  have r111_1 : (0 : ℤ) < 2 ^ p.toNat - 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ p.toNat - 1 : ℤ)) hH2)
  have s6 : (ArithmeticFunction.sigma 1 (2 ^ p.toNat - 1 : ℤ).toNat : ℤ) = 2 ^ p.toNat := by
    calc (ArithmeticFunction.sigma 1 (2 ^ p.toNat - 1 : ℤ).toNat : ℤ) = 2 ^ p.toNat - 1 + 1 := by exact (Parley.Items.Stdlib.Divisibility.thm_sigma_prime (p := (2 ^ p.toNat - 1 : ℤ)) (by parley_side) hH2)
      _ = 2 ^ p.toNat := by parley_ring
  -- 7. calculation
  have r117_1 : 0 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := p) (by parley_side))
  have r117_2 : Nat.Prime (2 : ℤ).toNat := by exact Parley.Items.Stdlib.Divisibility.mun_two_prime
  have r117_3 : (2 : ℤ) ≠ 1 := by parley_arith
  have s7 : ∃ m : ℕ, (m : ℚ) = (2 ^ (p - 1) : ℚ) ∧ (ArithmeticFunction.sigma 1 m : ℤ) = 2 ^ p.toNat - 1 := by
    have whole1 : ((2 : ℚ) : ℚ) ^ (p - 1).toNat = (2 ^ (p - 1) : ℚ) := by rw [← zpow_natCast, Int.toNat_of_nonneg r117_1]
    refine ⟨(2 ^ (p - 1).toNat), by (push_cast; simp only [whole1]; all_goals ring), ?_⟩
    exact (by
      try qify
      calc (ArithmeticFunction.sigma 1 (2 ^ (p - 1).toNat) : ℚ) = (∑ j ∈ Finset.Icc (0 : ℤ) (p - 1), (2 ^ j.toNat : ℚ)) := by exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_sigma_prime_power (p := (2 : ℤ)) (by parley_side) r117_2 (k := p - 1) (by parley_side))
        _ = (1 - 2 ^ (p - 1 + 1)) / (1 - 2) := by (have h := (Parley.Proofs.Wiedijk.GeometricSeries.GeometricSum.geometric_sum (a := (2 : ℝ)) (by parley_side) (n := p - 1) (by parley_side)); simp only [parley_zpow_toNat (n := p - 1 + 1) (h := add_nonneg (r117_1) (by norm_num))] at h ⊢; exact_mod_cast h)
        _ = (1 - 2 ^ p.toNat) / (1 - 2) := by (have h := congrArg (fun t : ℤ => (((1 - 2 ^ t) / (1 - 2)) : ℚ)) s1; simp only [parley_zpow_toNat (n := p - 1 + 1) (h := add_nonneg (r117_1) (by norm_num)), parley_zpow_toNat (n := p) (h := le_of_lt hH1)] at h ⊢; exact_mod_cast h)
        _ = 2 ^ p.toNat - 1 := by parley_ring)
  -- 8. algebra, from 3
  have r127_1 : 0 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := p) (by parley_side))
  have s8 : ((2 ^ p.toNat - 1) * 2 ^ p.toNat : ℚ) = 2 * (2 ^ (p - 1) * (2 ^ p.toNat - 1)) := by linear_combination (norm := parley_norm) (2 ^ p.toNat - 1) * s3
  -- 9. calculation
  have r131_1 : 0 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := p) (by parley_side))
  have r131_2 : (0 : ℤ) < 2 ^ p.toNat - 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ p.toNat - 1 : ℤ)) hH2)
  have s9 : ∃ m : ℕ, (m : ℚ) = (2 ^ (p - 1) * (2 ^ p.toNat - 1) : ℚ) ∧ (ArithmeticFunction.sigma 1 m : ℤ) = 2 * (m : ℤ) := by
    have whole1 : ((2 : ℚ) : ℚ) ^ (p - 1).toNat = (2 ^ (p - 1) : ℚ) := by rw [← zpow_natCast, Int.toNat_of_nonneg r131_1]
    have whole2 : ((((2 ^ p.toNat - 1 : ℤ)).toNat : ℕ) : ℚ) = (2 ^ p.toNat - 1 : ℚ) := by exact_mod_cast Int.toNat_of_nonneg (le_of_lt r131_2)
    have s5 := parley_witness_at s5 (((2 ^ (p - 1).toNat) : ℤ) : ℤ) (by (push_cast; simp only [whole1, whole2]; all_goals ring))
    have s7 := parley_witness_at_nat s7 (2 ^ (p - 1).toNat) (by (push_cast; simp only [whole1, whole2]; all_goals ring))
    refine ⟨((2 ^ (p - 1).toNat) * (((2 ^ p.toNat - 1 : ℤ)).toNat)), by (push_cast; simp only [whole1, whole2]; all_goals ring), ?_⟩
    exact (by
      calc (ArithmeticFunction.sigma 1 ((2 ^ (p - 1).toNat) * (((2 ^ p.toNat - 1 : ℤ)).toNat)) : ℤ) = (ArithmeticFunction.sigma 1 (2 ^ (p - 1).toNat) : ℤ) * (ArithmeticFunction.sigma 1 (((2 ^ p.toNat - 1 : ℤ)).toNat) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_sigma_multiplicative (m := (((2 ^ (p - 1).toNat) : ℤ) : ℤ)) (by parley_side) (n := (((((2 ^ p.toNat - 1 : ℤ)).toNat) : ℤ) : ℤ)) (by parley_side) (by parley_side))
        _ = ((((2 ^ p.toNat - 1 : ℤ)).toNat) : ℤ) * (ArithmeticFunction.sigma 1 (((2 ^ p.toNat - 1 : ℤ)).toNat) : ℤ) := by parley_subst s7
        _ = ((((2 ^ p.toNat - 1 : ℤ)).toNat) : ℤ) * 2 ^ p.toNat := by (have h := congrArg (fun t : ℤ => ((((2 ^ p.toNat - 1 : ℤ)).toNat) : ℤ) * t) s6; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 2 * (((2 ^ (p - 1).toNat) : ℤ) * ((((2 ^ p.toNat - 1 : ℤ)).toNat) : ℤ)) := by (qify; push_cast; simp only [whole1, whole2]; linear_combination (norm := parley_norm) s8))
  -- 10. def:perfect n := 2^(p − 1)·(2^p − 1), from 9
  have r140_1 : 0 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := p) (by parley_side))
  have r140_2 : (0 : ℤ) < 2 ^ p.toNat - 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ p.toNat - 1 : ℤ)) hH2)
  have whole1 : ((2 : ℚ) : ℚ) ^ (p - 1).toNat = (2 ^ (p - 1) : ℚ) := by rw [← zpow_natCast, Int.toNat_of_nonneg r140_1]
  have whole2 : ((((2 ^ p.toNat - 1 : ℤ)).toNat : ℕ) : ℚ) = (2 ^ p.toNat - 1 : ℚ) := by exact_mod_cast Int.toNat_of_nonneg (le_of_lt r140_2)
  have s9 := parley_witness_at_nat s9 ((2 ^ (p - 1).toNat) * (((2 ^ p.toNat - 1 : ℤ)).toNat)) (by (push_cast; simp only [whole1, whole2]; all_goals ring))
  refine ⟨((2 ^ (p - 1).toNat) * (((2 ^ p.toNat - 1 : ℤ)).toNat)), by (push_cast; simp only [whole1, whole2]; all_goals ring), ?_⟩
  exact (((Parley.Items.Stdlib.Divisibility.def_perfect (n := (((2 ^ (p - 1).toNat) : ℤ) * ((((2 ^ p.toNat - 1 : ℤ)).toNat) : ℤ) : ℤ)) (by parley_side))).mpr (by parley_side))

end Parley.Proofs.Wiedijk.PerfectNumbers.EuclidPerfect

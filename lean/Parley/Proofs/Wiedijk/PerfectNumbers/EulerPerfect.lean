module

public import AlgebraTactics
public import ArithTactics
public import InstanceTactics
public import NormTactics
public import PowerTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
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
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.GeometricSeries.GeometricSum
public import Parley.Proofs.Wiedijk.PerfectNumbers.OddPart
public import Parley.Proofs.Wiedijk.PerfectNumbers.ThreeDivisors

/-! Written from proofs/wiedijk/perfect-numbers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PerfectNumbers.EulerPerfect

theorem euler_perfect (n : ℤ) (hH1 : 0 < n) (hH2 : Even n) (hH3 : ArithmeticFunction.sigma 1 n.toNat = 2 * n.toNat) :
    (∃ p : ℤ, 0 < p ∧ (Nat.Prime (2 ^ p.toNat - 1 : ℤ).toNat ∧ (n : ℚ) = 2 ^ (p - 1) * (2 ^ p.toNat - 1))) := by
  -- 1. obtain k, m: thm:odd-part
  obtain ⟨k, s1a, m, s1b, ⟨s1c, s1d⟩⟩ := (Parley.Proofs.Wiedijk.PerfectNumbers.OddPart.odd_part (n := n) hH1)
  -- 2. contradiction
  have s2 : k ≠ 0 := by
    intro hS1
    -- 2.1. substitute k = 0 (S1) into line 1
    have s2_1 : n = 2 ^ 0 * m := by (have h := Eq.subst (motive := (fun t : ℤ => n = 2 ^ t.toNat * m)) hS1 s1d; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.2. calculation
    have s2_2 : n = m := by
      calc n = 2 ^ 0 * m := by exact s2_1
        _ = m := by parley_ring
    -- 2.3. substitute n = m (line 2.2) into line 1
    have s2_3 : Odd n := by (have h := Eq.subst (motive := (fun t : ℤ => Odd t)) s2_2.symm s1c; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.4. mun:not-both, from H2
    have s2_4 : ¬ Odd n := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := n) hH2)
    exact s2_4 s2_3
  -- 3. mun:nat0-nonzero m := k, from 2
  have s3 : 0 < k := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := k) s1a s2)
  have hD2_kind : 0 < k + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := k) s1a)
  set p : ℤ := k + 1 with hD2
  have hD2_pos := hD2_kind
  -- 4. inequalities, from D2, 3
  have s4 : 1 < p := by linarith only [s3, hD2]
  -- 5. mun:power-order a := 2, m := 1, n := p, from 4
  have r352_1 : (2 : ℤ) > 1 := by parley_arith
  have s5 : (2 ^ 1 : ℤ) < 2 ^ p.toNat := by (have h := ((Parley.Items.Stdlib.Numbers.mun_power_order (a := (2 : ℚ)) (m := (1 : ℤ)) (n := p) (by parley_side))).mp s4; simp only [parley_zpow_toNat (n := (1 : ℤ)) (h := by norm_num), parley_zpow_toNat (n := p) (h := le_of_lt (lt_of_le_of_lt (by norm_num) s4))] at h ⊢; exact_mod_cast h)
  -- 6. inequalities, from 5
  have s6 : (2 ^ p.toNat - 1 : ℤ) > 1 := by linarith only [s5]
  -- 7. mun:pos-int-nat
  have r359_1 : (0 : ℤ) < 2 ^ p.toNat - 1 := by linarith only [s6]
  have s7 : (0 : ℤ) < 2 ^ p.toNat - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (2 ^ p.toNat - 1 : ℤ)) r359_1)
  -- 8. mun:exponent-step a := 2, m := k, from D2
  have s8 : (2 ^ p.toNat : ℤ) = 2 ^ k.toNat * 2 := by
    try simp only [hD2] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) s1a)
  -- 9. contradiction
  have s9 : ¬ (2 : ℤ) ∣ (2 ^ p.toNat - 1 : ℤ) := by
    intro hS2
    -- 9.1. mun:divides-self n := 2
    have s9_1 : (2 : ℤ) ∣ (2 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (2 : ℤ)))
    -- 9.2. mun:divides-multiple e := 2, a := 2, x := 2^k, from 9.1
    have s9_2 : (2 : ℤ) ∣ (2 * 2 ^ k.toNat : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (2 : ℤ)) (a := (2 : ℤ)) (x := (2 ^ k.toNat : ℤ)) s9_1)
    -- 9.3. substitute
    have s9_3 : (2 : ℤ) ∣ (2 ^ p.toNat : ℤ) := by
      have c1 : (2 * 2 ^ k.toNat : ℤ) = 2 ^ p.toNat := by linear_combination (norm := parley_norm) (-1) * s8
      have row1 : (2 : ℤ) ∣ (2 ^ p.toNat : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (2 : ℤ) ∣ t)) c1 s9_2; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 9.4. mun:divides-difference d := 2, a := 2^p, b := 2^p − 1, from S2, 9.3
    have s9_4 : (2 : ℤ) ∣ (2 ^ p.toNat - (2 ^ p.toNat - 1) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (2 : ℤ)) (a := (2 ^ p.toNat : ℤ)) (b := (2 ^ p.toNat - 1 : ℤ)) s9_3 hS2)
    -- 9.5. substitute
    have s9_5 : (2 : ℤ) ∣ (1 : ℤ) := by
      have c1 : (2 ^ p.toNat - (2 ^ p.toNat - 1) : ℤ) = 1 := by parley_ring
      have row1 : (2 : ℤ) ∣ (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (2 : ℤ) ∣ t)) c1 s9_4; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 9.6. mun:divides-one d := 2, from 9.5
    have s9_6 : (2 : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (2 : ℤ)) (by norm_num) s9_5)
    exact absurd s9_6 (by norm_num)
  -- 10. mun:prime-coprime p := 2, a := 2^p − 1, from 9
  have r392_1 : Nat.Prime (2 : ℤ).toNat := by exact Parley.Items.Stdlib.Divisibility.mun_two_prime
  have s10 : (Int.gcd (2 : ℤ) (2 ^ p.toNat - 1 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (2 : ℤ)) (by norm_num) r392_1 (a := (2 ^ p.toNat - 1 : ℤ)) s9)
  -- 11. mun:coprime-power a := 2, b := 2^p − 1, k := p, from 10
  have s11 : (Int.gcd (2 ^ p.toNat : ℤ) (2 ^ p.toNat - 1 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (2 : ℤ)) (b := (2 ^ p.toNat - 1 : ℤ)) (k := p) (le_of_lt hD2_pos) s10)
  -- 12. mun:prime-coprime p := 2, a := m
  have r399_1 : Nat.Prime (2 : ℤ).toNat := by exact Parley.Items.Stdlib.Divisibility.mun_two_prime
  have r399_2 : ¬ (2 : ℤ) ∣ m := by exact (Parley.Items.Stdlib.Divisibility.mun_odd_not_divisible (n := m) s1c)
  have s12 : (Int.gcd (2 : ℤ) m : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (2 : ℤ)) (by norm_num) r399_1 (a := m) r399_2)
  -- 13. mun:coprime-power a := 2, b := m, from 12
  have s13 : (Int.gcd (2 ^ k.toNat : ℤ) m : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (2 : ℤ)) (b := m) (k := k) s1a s12)
  -- 14. calculation
  have r407_1 : Nat.Prime (2 : ℤ).toNat := by exact Parley.Items.Stdlib.Divisibility.mun_two_prime
  have r407_2 : (2 : ℤ) ≠ 1 := by parley_arith
  have s14 : (ArithmeticFunction.sigma 1 (2 ^ k.toNat) : ℤ) = 2 ^ p.toNat - 1 := by
    try qify
    calc (ArithmeticFunction.sigma 1 (2 ^ k.toNat) : ℚ) = (∑ j ∈ Finset.Icc (0 : ℤ) k, (2 ^ j.toNat : ℚ)) := by
          have hI : (ArithmeticFunction.sigma 1 (2 ^ k.toNat) : ℚ) = (∑ j ∈ Finset.Icc (0 : ℤ) k, (2 ^ j.toNat : ℚ)) := by parley_instance_cast ((Parley.Items.Stdlib.Divisibility.thm_sigma_prime_power (p := (2 : ℤ)) (by norm_num) r407_1 (k := k) s1a))
          exact hI
      _ = (1 - 2 ^ (k + 1).toNat) / (1 - 2) := by
          have hI : (∑ j ∈ Finset.Icc (0 : ℤ) k, (2 ^ j.toNat : ℚ)) = (1 - 2 ^ (k + 1).toNat) / (1 - 2) := by parley_instance_real ((Parley.Proofs.Wiedijk.GeometricSeries.GeometricSum.geometric_sum (a := (2 : ℝ)) (by parley_side) (n := k) s1a))
          exact hI
      _ = 2 ^ p.toNat - 1 := by
          try simp only [hD2] at r407_1 r407_2 ⊢
          try push_cast at r407_1 r407_2 ⊢
          parley_ring
  -- 15. calculation
  have s15 : (2 ^ p.toNat - 1) * (ArithmeticFunction.sigma 1 m.toNat : ℤ) = 2 ^ p.toNat * m := by
    calc (2 ^ p.toNat - 1) * (ArithmeticFunction.sigma 1 m.toNat : ℤ) = (ArithmeticFunction.sigma 1 (2 ^ k.toNat) : ℤ) * (ArithmeticFunction.sigma 1 m.toNat : ℤ) := by (have h := congrArg (fun t : ℤ => t * (ArithmeticFunction.sigma 1 m.toNat : ℤ)) s14.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (ArithmeticFunction.sigma 1 (2 ^ k.toNat * m).toNat : ℤ) := by
          have hI : (ArithmeticFunction.sigma 1 (2 ^ k.toNat * m).toNat : ℤ) = (ArithmeticFunction.sigma 1 (2 ^ k.toNat) : ℤ) * (ArithmeticFunction.sigma 1 m.toNat : ℤ) := by parley_instance ((Parley.Items.Stdlib.Divisibility.thm_sigma_multiplicative (m := (2 ^ k.toNat : ℤ)) (by parley_side) (n := m) s1b s13))
          exact hI.symm
      _ = (ArithmeticFunction.sigma 1 n.toNat : ℤ) := by (have h := congrArg (fun t : ℤ => (ArithmeticFunction.sigma 1 t.toNat : ℤ)) s1d.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 2 * n := by exact ((Parley.Items.Stdlib.Divisibility.def_perfect (n := n) hH1)).mp hH3
      _ = 2 ^ p.toNat * m := by linear_combination (norm := parley_norm) (2) * s1d + (-m) * s8
  -- 16. mun:sigma-nat n := m
  have s16 : 0 < (ArithmeticFunction.sigma 1 m.toNat : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_sigma_nat (n := m) s1b)
  -- 17. algebra, from 15
  have s17 : m * 2 ^ p.toNat = (2 ^ p.toNat - 1) * (ArithmeticFunction.sigma 1 m.toNat : ℤ) := by linear_combination (norm := parley_norm) (-1) * s15
  -- 18. def:divides d := 2^p − 1, n := m·2^p, from 16, 17
  have s18 : (2 ^ p.toNat - 1 : ℤ) ∣ m * 2 ^ p.toNat := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 ^ p.toNat - 1 : ℤ)) (n := m * 2 ^ p.toNat))).mpr ⟨(ArithmeticFunction.sigma 1 m.toNat : ℤ), s17⟩
  -- 19. thm:coprime-divides x := m, c := 2^p, n := 2^p − 1, from 7, 11, 18
  have s19 : (2 ^ p.toNat - 1 : ℤ) ∣ m := by exact (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := m) (c := (2 ^ p.toNat : ℤ)) (n := (2 ^ p.toNat - 1 : ℤ)) s7 s18 s11)
  have hD3_kind : ∃ m₀ : ℤ, 0 < m₀ ∧ (m₀ : ℚ) = (m : ℚ) / (2 ^ p.toNat - 1) := by
    have hI : ∃ m₀ : ℤ, 0 < m₀ ∧ (m₀ : ℚ) = (m : ℚ) / (2 ^ p.toNat - 1) := by parley_instance (((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := m) s1b (d := (2 ^ p.toNat - 1 : ℤ)) s7)).mp s19)
    exact hI
  obtain ⟨c, hD3_pos, hD3⟩ := hD3_kind
  -- 20. algebra, from D3
  have r440_1 : (2 ^ p.toNat - 1 : ℤ) ≠ 0 := by exact s7.ne'
  have s20 : m = (2 ^ p.toNat - 1) * c := by qify at *; linear_combination (norm := parley_field) (-(2 ^ p.toNat) + 1) * hD3
  -- 21. algebra, from 15, 20
  have s21 : (ArithmeticFunction.sigma 1 m.toNat : ℤ) * (2 ^ p.toNat - 1) = 2 ^ p.toNat * c * (2 ^ p.toNat - 1) := by linear_combination (norm := parley_norm) s15 + (2 ^ p.toNat) * s20
  -- 22. calculation
  have r448_2 : (2 ^ p.toNat - 1 : ℤ) ≠ 0 := by exact s7.ne'
  have s22 : (ArithmeticFunction.sigma 1 m.toNat : ℤ) = m + c := by
    calc (ArithmeticFunction.sigma 1 m.toNat : ℤ) = 2 ^ p.toNat * c := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (ArithmeticFunction.sigma 1 m.toNat : ℤ)) (b := 2 ^ p.toNat * c) (c := (2 ^ p.toNat - 1 : ℤ)) (by parley_side) r448_2)
      _ = m + c := by linear_combination (norm := parley_norm) (-1) * s20
  -- 23. contradiction
  have s23 : c = 1 := by
    by_contra (hS3 : c ≠ 1)
    -- 23.1. inequalities, from 6
    have s23_1 : (2 ^ p.toNat - 1 - 1 : ℤ) > 0 := by linarith only [s6]
    -- 23.2. mun:product-positive x := 2^p − 1 − 1, y := c, from D3, 23.1
    have s23_2 : (2 ^ p.toNat - 1 - 1) * c > 0 := by exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (2 ^ p.toNat - 1 - 1 : ℚ)) (y := (c : ℚ)) (by exact_mod_cast gt_iff_lt.mp s23_1) (by parley_side))
    -- 23.3. substitute
    have s23_3 : m - c > 0 := by
      have c1 : (2 ^ p.toNat - 1 - 1) * c = m - c := by linear_combination (norm := parley_norm) (-1) * s20
      have row1 : m - c > 0 := by (have h := Eq.subst (motive := (fun t : ℤ => t > 0)) c1 s23_2; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 23.4. inequalities
    have s23_4 : c < m := by linarith only [s23_3]
    -- 23.5. inequalities, from D3, S3
    have r477_1 : (2 ^ p.toNat - 1 : ℤ) ≠ 0 := by exact s7.ne'
    have s23_5 : 1 < c := Or.elim (Ne.lt_or_gt hS3) (fun h1 => by linarith only [hD3_pos, h1]) (fun h1 => by linarith only [hD3_pos, h1])
    -- 23.6. algebra, from 20
    have s23_6 : m = c * (2 ^ p.toNat - 1) := by linear_combination (norm := parley_norm) s20
    -- 23.7. def:divides d := c, n := m, from 23.6
    have s23_7 : c ∣ m := ((Parley.Items.Stdlib.Divisibility.def_divides (d := c) (n := m))).mpr ⟨(2 ^ p.toNat - 1 : ℤ), s23_6⟩
    -- 23.8. thm:three-divisors e := c, from 23.4, 23.5, 23.7
    have s23_8 : (ArithmeticFunction.sigma 1 m.toNat : ℤ) ≥ 1 + c + m := by exact (Parley.Proofs.Wiedijk.PerfectNumbers.ThreeDivisors.three_divisors (m := m) s1b (e := c) hD3_pos s23_7 s23_5 s23_4)
    -- 23.9. transitivity, from 23.8, 22
    have s23_9 : 1 + c + m ≤ m + c := by exact LE.le.trans_eq s23_8 s22
    -- 23.10. inequalities
    have s23_10 : (1 : ℤ) ≤ 0 := by linarith only [s23_9]
    exact absurd s23_10 (by norm_num)
  -- 24. substitute c = 1 (line 23) into line 20
  have s24 : m = 2 ^ p.toNat - 1 := by (have h := Eq.subst (motive := (fun t : ℤ => m = (2 ^ p.toNat - 1) * t)) s23 s20; push_cast [mul_one] at h ⊢; all_goals exact_mod_cast h)
  -- 25. substitute c = 1 (line 23) into line 22
  have s25 : (ArithmeticFunction.sigma 1 m.toNat : ℤ) = m + 1 := by (have h := Eq.subst (motive := (fun t : ℤ => (ArithmeticFunction.sigma 1 m.toNat : ℤ) = m + t)) s23 s22; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 26. proof
  have s26 : ∀ d : ℤ, 0 < d → d ∣ m → d = 1 ∨ d = m := by
    intro d hK1
    intro hA1
    by_contra hS4
    -- 26.1. mun:not-either P := d = 1, Q := d = m, from S4
    have s26_1a : d ≠ 1 := by
      have hI : d ≠ 1 := by parley_instance ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = m))).mp hS4).1)
      exact hI
    have s26_1b : d ≠ m := by
      have hI : d ≠ m := by parley_instance ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = m))).mp hS4).2)
      exact hI
    -- 26.2. mun:divides-le e := d, from A1
    have s26_2 : d ≤ m := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := d) hK1 (m := m) s1b hA1)
    -- 26.3. inequalities, from K1, 26.1
    have s26_3 : 1 < d := Or.elim (Ne.lt_or_gt s26_1a) (fun h1 => by linarith only [hK1, h1]) (fun h1 => by linarith only [hK1, h1])
    -- 26.4. inequalities, from 26.1, 26.2
    have s26_4 : d < m := Or.elim (Ne.lt_or_gt s26_1b) (fun h1 => by linarith only [s26_2, h1]) (fun h1 => by linarith only [s26_2, h1])
    -- 26.5. thm:three-divisors e := d, from A1, 26.3, 26.4
    have s26_5 : (ArithmeticFunction.sigma 1 m.toNat : ℤ) ≥ 1 + d + m := by exact (Parley.Proofs.Wiedijk.PerfectNumbers.ThreeDivisors.three_divisors (m := m) s1b (e := d) hK1 hA1 s26_3 s26_4)
    -- 26.6. transitivity, from 26.5, 25
    have s26_6 : 1 + d + m ≤ m + 1 := by exact LE.le.trans_eq s26_5 s25
    -- 26.7. inequalities
    have s26_7 : d ≤ 0 := by linarith only [s26_6]
    -- 26.8. inequalities, from 26.7
    have s26_8 : ¬ 1 < d := by linarith only [s26_7]
    exact s26_8 s26_3
  -- 27. substitute m = 2^p − 1 (line 24) into line 6
  have s27 : m > 1 := by (have h := Eq.subst (motive := (fun t : ℤ => t > 1)) s24.symm s6; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 28. def:prime p := m, from 26, 27
  have s28 : Nat.Prime m.toNat := ((Parley.Items.Stdlib.Divisibility.def_prime (p := m) s1b)).mpr ⟨s27, s26⟩
  -- 29. substitute m = 2^p − 1 (line 24) into line 28
  have s29 : Nat.Prime (2 ^ p.toNat - 1 : ℤ).toNat := by (have h := Eq.subst (motive := (fun t : ℤ => Nat.Prime t.toNat)) s24 s28; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 30. algebra, from D2
  have s30 : p - 1 = k := by
    try simp only [hD2] at ⊢
    try push_cast at ⊢
    parley_ring
  -- 31. calculation
  have s31 : (n : ℚ) = 2 ^ (p - 1) * (2 ^ p.toNat - 1) := by
    calc (n : ℚ) = 2 ^ k.toNat * (m : ℚ) := by parley_side
      _ = 2 ^ (p - 1) * (m : ℚ) := by (have h := congrArg (fun t : ℤ => 2 ^ t * (m : ℚ)) s30.symm; simp only [parley_zpow_toNat (n := k) (h := s1a)] at h ⊢; exact_mod_cast h)
      _ = 2 ^ (p - 1) * (2 ^ p.toNat - 1) := by
          have e_w : (m : ℚ) = 2 ^ p.toNat - 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s24; push_cast at h; linear_combination (norm := parley_norm) h
          (have h := congrArg (fun t : ℚ => 2 ^ (p - 1) * t) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 32. exhibit, from 29, 31
  exact ⟨p, hD2_pos, ⟨s29, s31⟩⟩

end Parley.Proofs.Wiedijk.PerfectNumbers.EulerPerfect

module

public import AlgebraTactics
public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.PrimePowerNotLess

theorem prime_power_not_less (p : ℤ) (hH1 : 0 < p) (hH2 : Nat.Prime p.toNat) (a : ℤ) (hH3 : 0 ≤ a) (a' : ℤ) (hH4 : 0 ≤ a') (m : ℤ) (m' : ℤ) (hH7 : (Int.gcd m p : ℤ) = 1) (hH8 : p ^ a.toNat * m = p ^ a'.toNat * m') :
    ¬ a < a' := by
  -- 1. def:prime, from H2
  have s1 : p > 1 ∧ (∀ d : ℤ, 0 < d → d ∣ p → d = 1 ∨ d = p) := by exact ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) hH1)).mp hH2
  -- 2. restate 1
  have s2 : p > 1 := by parley_side
  -- 3. contradiction
  intro hS
  -- 3.1. inequalities
  have s3_1 : 0 < a' - a := by linarith only [hS]
  -- 3.2. mun:pos-int-nat m := a′ − a, from 3.1
  have s3_2 : 0 < a' - a := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a' - a) s3_1)
  -- 3.3. mun:power-nat a := p, m := a′ − a, from 3.2
  have s3_3 : ∃ m : ℤ, 0 < m ∧ (m : ℚ) = (p : ℚ) ^ (a' - a) := by
    have whole1 : ((p : ℚ) : ℚ) ^ (a' - a).toNat = (p : ℚ) ^ (a' - a) := by rw [← zpow_natCast, Int.toNat_of_nonneg (le_of_lt s3_2)]
    refine ⟨(p ^ (a' - a).toNat), ?_, by (push_cast; simp only [whole1]; all_goals ring)⟩
    (exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := p) hH1 (m := a' - a) (le_of_lt s3_2)))
  -- 3.4. mun:exponent-sum a := p, m := a, n := a′ − a, from 3.2
  have s3_4 : (p : ℚ) ^ (a + (a' - a)) = (p : ℚ) ^ a.toNat * (p : ℚ) ^ (a' - a) := by (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) hH3 (n := a' - a) (le_of_lt s3_2)); simp only [parley_zpow_toNat (n := a + (a' - a)) (h := add_nonneg (hH3) (le_of_lt s3_2)), parley_zpow_toNat (n := a' - a) (h := le_of_lt s3_2)] at h ⊢; exact_mod_cast h)
  -- 3.5. substitute
  have s3_5 : (p : ℚ) ^ a'.toNat = (p : ℚ) ^ a.toNat * (p : ℚ) ^ (a' - a) := by
    have c1 : a + (a' - a) = a' := by parley_ring
    have row1 : (p : ℚ) ^ a'.toNat = (p : ℚ) ^ a.toNat * (p : ℚ) ^ (a' - a) := by (have h := Eq.subst (motive := (fun t : ℤ => (p : ℚ) ^ t = (p : ℚ) ^ a.toNat * (p : ℚ) ^ (a' - a))) c1 s3_4; simp only [parley_zpow_toNat (n := a') (h := hH4), parley_zpow_toNat (n := a' - a) (h := le_of_lt (lt_of_le_of_lt (by norm_num) s3_1))] at h ⊢; exact_mod_cast h)
    exact row1
  -- 3.6. algebra, from H8, 3.5
  have s3_6 : (m : ℚ) * (p : ℚ) ^ a.toNat = (p : ℚ) ^ (a' - a) * (m' : ℚ) * (p : ℚ) ^ a.toNat := by
    have hH8_w : (p : ℚ) ^ a.toNat * (m : ℚ) = (p : ℚ) ^ a'.toNat * (m' : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) hH8; push_cast at h; linear_combination (norm := parley_norm) h
    linear_combination (norm := parley_norm) hH8_w + ((m' : ℚ)) * s3_5
  -- 3.7. mun:power-positive a := p, m := a
  have r423_1 : 0 < p := by exact hH1
  have s3_7 : p ^ a.toNat > 0 := by (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (p : ℚ)) (m := a) (by exact_mod_cast r423_1)); simp only [parley_zpow_toNat (n := a) (h := hH3)] at h ⊢; exact_mod_cast h)
  -- 3.8. inequalities
  have s3_8 : p ^ a.toNat ≠ 0 := ne_of_gt (by linarith only [s3_7])
  -- 3.9. mun:multiply-cancel a := m, b := p^(a′ − a)·m′, c := p^a, from 3.6, 3.8
  have s3_9 : (m : ℚ) = (p : ℚ) ^ (a' - a) * (m' : ℚ) := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) s3_6 (by exact_mod_cast s3_8))
  -- 3.10. mun:divides-self n := p
  have s3_10 : p ∣ p := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := p))
  -- 3.11. thm:prime-divides-power a := p, n := a′ − a, from H2, 3.2, 3.10
  have s3_11 : ∃ m : ℤ, (m : ℚ) = (p : ℚ) ^ (a' - a) ∧ p ∣ m := by
    have whole1 : ((p : ℚ) : ℚ) ^ (a' - a).toNat = (p : ℚ) ^ (a' - a) := by rw [← zpow_natCast, Int.toNat_of_nonneg (le_of_lt s3_2)]
    refine ⟨(p ^ (a' - a).toNat), by (push_cast; simp only [whole1]; all_goals ring), ?_⟩
    exact (((Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := p) hH1 hH2 (a := p) (n := a' - a) s3_2)).mpr s3_10)
  -- 3.12. mun:divides-multiple e := p, a := p^(a′ − a), x := m′, from 3.11
  have r443_1 : ∃ m : ℤ, (m : ℚ) = (p : ℚ) ^ (a' - a) := by
    have whole1 : ∃ m : ℤ, (m : ℚ) = (p : ℚ) ^ (a' - a) := by obtain ⟨m, _, hm⟩ := s3_3; exact ⟨m, by exact_mod_cast hm⟩
    exact ⟨(Classical.choose whole1 : ℤ), by (push_cast; simp only [Classical.choose_spec whole1]; all_goals ring)⟩
  have s3_12 : ∃ m : ℤ, (m : ℚ) = (p : ℚ) ^ (a' - a) * (m' : ℚ) ∧ p ∣ m := by
    have whole1 : ∃ m : ℤ, (m : ℚ) = (p : ℚ) ^ (a' - a) := by obtain ⟨m, hm⟩ := r443_1; exact ⟨m, by exact_mod_cast hm⟩
    have s3_11 := parley_witness_at s3_11 (Classical.choose whole1 : ℤ) (by (push_cast; simp only [Classical.choose_spec whole1]; all_goals ring))
    refine ⟨((Classical.choose whole1 : ℤ) * m'), by (push_cast; simp only [Classical.choose_spec whole1]; all_goals ring), ?_⟩
    (exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := p) (a := (Classical.choose whole1 : ℤ)) (x := m') s3_11))
  -- 3.13. substitute m = p^(a′ − a)·m′ (line 3.9) into line 3.12
  have s3_13 : p ∣ m := by exact parley_witness_at (Eq.subst (motive := (fun t : ℚ => ∃ m : ℤ, (m : ℚ) = t ∧ p ∣ m)) s3_9.symm s3_12) m (by norm_cast)
  -- 3.14. thm:divides-gcd d := p, a := m, b := p, from 3.10, 3.13
  have s3_14 : p ∣ (Int.gcd m p : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := p) (a := m) (b := p) s3_13 s3_10)
  -- 3.15. substitute gcd(m, p) = 1 (H7) into line 3.14
  have s3_15 : p ∣ (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => p ∣ t)) hH7 s3_14; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 3.16. substitute
  have s3_16 : (1 : ℤ) > 1 := by
    have c1 : p = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) hH1 s3_15)
    have row1 : (1 : ℤ) > 1 := by (have h := Eq.subst (motive := (fun t : ℤ => t > 1)) c1 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  exact absurd s3_16 (by norm_num)

end Parley.Stdlib.Divisibility.PrimePowerNotLess

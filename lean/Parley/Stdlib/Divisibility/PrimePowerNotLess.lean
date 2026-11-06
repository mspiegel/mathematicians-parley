module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.PrimePowerNotLess

set_option maxHeartbeats 400000 in
theorem prime_power_not_less (p : ℤ) (hH1 : 0 < p) (hH2 : Nat.Prime p.toNat) (a : ℤ) (hH3 : 0 ≤ a) (a' : ℤ) (hH4 : 0 ≤ a') (m : ℤ) (m' : ℤ) (hH7 : (Int.gcd m p : ℤ) = 1) (hH8 : p ^ a.toNat * m = p ^ a'.toNat * m') :
    ¬ a < a' := by
  -- 1. def:prime, from H2
  have s1 : p > 1 ∧ (∀ d : ℤ, 0 < d → d ∣ p → d = 1 ∨ d = p) := by first | exact ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side); parley_side)
  -- 2. restate 1
  have s2 : p > 1 := by parley_side
  -- 3. contradiction
  have s3 : ¬ a < a' := by
    by_contra hc_hS
    have hS : a < a' := by parley_suppose hc_hS
    -- 3.1. inequalities
    have s3_1 : 0 < a' - a := by parley_order
    -- 3.2. mun:pos-int-nat m := a′ − a, from 3.1
    have s3_2 : 0 < a' - a := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a' - a) s3_1) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a' - a) s3_1)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a' - a) s3_1) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a' - a) s3_1) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a' - a) s3_1); parley_side)
    -- 3.3. mun:power-nat a := p, m := a′ − a, from 3.2
    have s3_3 : ∃ m : ℤ, 0 < m ∧ (m : ℚ) = (p : ℚ) ^ (a' - a) := by
      have whole1 : ((p : ℚ) : ℚ) ^ (a' - a).toNat = (p : ℚ) ^ (a' - a) := by rw [← zpow_natCast, Int.toNat_of_nonneg (le_of_lt s3_2)]
      refine ⟨(p ^ (a' - a).toNat), ?_, by first | (push_cast; simp only [whole1]; done) | (push_cast; simp only [whole1]; ring)⟩
      (first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := p) (by parley_side) (m := a' - a) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := p) (by parley_side) (m := a' - a) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := p) (by parley_side) (m := a' - a) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := p) (by parley_side) (m := a' - a) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := p) (by parley_side) (m := a' - a) (by parley_side)); parley_side))
    -- 3.4. mun:exponent-sum a := p, m := a, n := a′ − a, from 3.2
    have s3_4 : (p : ℚ) ^ (a + (a' - a)) = (p : ℚ) ^ a.toNat * (p : ℚ) ^ (a' - a) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) (by parley_side) (n := a' - a) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) (by parley_side) (n := a' - a) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) (by parley_side) (n := a' - a) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) (by parley_side) (n := a' - a) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) (by parley_side) (n := a' - a) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) (by parley_side) (n := a' - a) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) (by parley_side) (n := a' - a) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) (by parley_side) (n := a' - a) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) (by parley_side) (n := a' - a) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) (by parley_side) (n := a' - a) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (p : ℚ)) (m := a) (by parley_side) (n := a' - a) (by parley_side)); parley_side)
    -- 3.5. substitute
    have s3_5 : (p : ℚ) ^ a'.toNat = (p : ℚ) ^ a.toNat * (p : ℚ) ^ (a' - a) := by
      have c1 : a + (a' - a) = a' := by parley_ring
      have c1_w : (a : ℚ) + ((a' : ℚ) - (a : ℚ)) = (a' : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
      have row1 : (p : ℚ) ^ a'.toNat = (p : ℚ) ^ a.toNat * (p : ℚ) ^ (a' - a) := by first | parley_put_at c1_w s3_4 | parley_put_at c1 s3_4 | parley_subst_at c1_w s3_4 | parley_subst_at c1 s3_4
      exact row1
    -- 3.6. algebra, from H8, 3.5
    have s3_6 : (m : ℚ) * (p : ℚ) ^ a.toNat = (p : ℚ) ^ (a' - a) * (m' : ℚ) * (p : ℚ) ^ a.toNat := by
      have hH8_w : (p : ℚ) ^ a.toNat * (m : ℚ) = (p : ℚ) ^ a'.toNat * (m' : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) hH8; push_cast at h; linear_combination (norm := parley_norm) h
      linear_combination (norm := parley_norm) hH8_w + ((m' : ℚ)) * s3_5
    -- 3.7. mun:power-positive a := p, m := a
    have r423_1 : 0 < p := by parley_side
    have s3_7 : p ^ a.toNat > 0 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (p : ℚ)) (m := a) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (p : ℚ)) (m := a) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (p : ℚ)) (m := a) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (p : ℚ)) (m := a) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (p : ℚ)) (m := a) (by parley_side)); parley_side)
    -- 3.8. inequalities
    have s3_8 : p ^ a.toNat ≠ 0 := by parley_side
    -- 3.9. mun:multiply-cancel a := m, b := p^(a′ − a)·m′, c := p^a, from 3.6, 3.8
    have s3_9 : (m : ℚ) = (p : ℚ) ^ (a' - a) * (m' : ℚ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) (by parley_side) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) (by parley_side) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (m : ℚ)) (b := (p : ℚ) ^ (a' - a) * (m' : ℚ)) (c := (p : ℚ) ^ a.toNat) (by parley_side) (by parley_side)); parley_side)
    -- 3.10. mun:divides-self n := p
    have s3_10 : p ∣ p := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := p)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := p))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := p)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := p)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := p)); parley_side)
    -- 3.11. thm:prime-divides-power a := p, n := a′ − a, from H2, 3.2, 3.10
    have s3_11 : ∃ m : ℤ, (m : ℚ) = (p : ℚ) ^ (a' - a) ∧ p ∣ m := by
      have whole1 : ((p : ℚ) : ℚ) ^ (a' - a).toNat = (p : ℚ) ^ (a' - a) := by rw [← zpow_natCast, Int.toNat_of_nonneg (le_of_lt s3_2)]
      refine ⟨(p ^ (a' - a).toNat), by first | (push_cast; simp only [whole1]; done) | (push_cast; simp only [whole1]; ring), ?_⟩
      (first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := p) (by parley_side) hH2 (a := p) (n := a' - a) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := p) (by parley_side) hH2 (a := p) (n := a' - a) (by parley_side))).mpr (by parley_side); parley_side))
    -- 3.12. mun:divides-multiple e := p, a := p^(a′ − a), x := m′, from 3.11
    have r443_1 : ∃ m : ℤ, (m : ℚ) = (p : ℚ) ^ (a' - a) := by
      have whole1 : ∃ m : ℤ, (m : ℚ) = (p : ℚ) ^ (a' - a) := by obtain ⟨m, _, hm⟩ := s3_3; exact ⟨m, by exact_mod_cast hm⟩
      exact ⟨(Classical.choose whole1 : ℤ), by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring)⟩
    have s3_12 : ∃ m : ℤ, (m : ℚ) = (p : ℚ) ^ (a' - a) * (m' : ℚ) ∧ p ∣ m := by
      have whole1 : ∃ m : ℤ, (m : ℚ) = (p : ℚ) ^ (a' - a) := by obtain ⟨m, hm⟩ := r443_1; exact ⟨m, by exact_mod_cast hm⟩
      have s3_11 := parley_witness_at s3_11 (Classical.choose whole1 : ℤ) (by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring))
      refine ⟨((Classical.choose whole1 : ℤ) * m'), by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring), ?_⟩
      (first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := p) (a := (Classical.choose whole1 : ℤ)) (x := m') s3_11) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := p) (a := (Classical.choose whole1 : ℤ)) (x := m') s3_11)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := p) (a := (Classical.choose whole1 : ℤ)) (x := m') s3_11) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := p) (a := (Classical.choose whole1 : ℤ)) (x := m') s3_11) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := p) (a := (Classical.choose whole1 : ℤ)) (x := m') s3_11); parley_side))
    -- 3.13. substitute m = p^(a′ − a)·m′ (line 3.9) into line 3.12
    have s3_13 : p ∣ m := by first | parley_subst_at s3_9 s3_12 | exact parley_witness_at s3_12 (m) (by push_cast; linear_combination (norm := parley_norm) s3_9) | exact parley_witness_at s3_12 (m) (by push_cast; linear_combination (norm := parley_norm) -s3_9)
    -- 3.14. thm:divides-gcd d := p, a := m, b := p, from 3.10, 3.13
    have s3_14 : p ∣ (Int.gcd m p : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := p) (a := m) (b := p) s3_13 s3_10) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := p) (a := m) (b := p) s3_13 s3_10)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := p) (a := m) (b := p) s3_13 s3_10) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := p) (a := m) (b := p) s3_13 s3_10) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := p) (a := m) (b := p) s3_13 s3_10); parley_side)
    -- 3.15. substitute gcd(m, p) = 1 (H7) into line 3.14
    have s3_15 : p ∣ (1 : ℤ) := by first | parley_subst_at hH7 s3_14 | (have e_nat : Int.gcd m p = 1 := by exact_mod_cast hH7; parley_subst_at e_nat s3_14)
    -- 3.16. substitute
    have s3_16 : (1 : ℤ) > 1 := by
      have c1 : p = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s3_15) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s3_15); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s3_15); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s3_15) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s3_15)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s3_15); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s3_15); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s3_15); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s3_15); parley_side)
      have row1 : (1 : ℤ) > 1 := by parley_subst_at c1 s2
      exact row1
    exact absurd s3_16 (by norm_num)
    all_goals parley_side
  all_goals exact s3

end Parley.Stdlib.Divisibility.PrimePowerNotLess

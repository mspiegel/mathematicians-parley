module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Hammack.MersennePrimeExponent.PowerMultipleQuotient
public import Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound

/-! Written from proofs/hammack/mersenne-prime-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MersennePrimeExponent.PrimeExponent

set_option maxHeartbeats 800000 in
theorem prime_exponent (n : ℕ) (hH1 : 0 < n) (hH2 : Nat.Prime (2 ^ n - 1 : ℤ).toNat) :
    Nat.Prime n := by
  -- 1. mun:prime-nat p := 2^n − 1, from H2
  have s1 : (0 : ℤ) < 2 ^ n - 1 := by first | exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ n - 1 : ℤ)) hH2) | exact ((Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ n - 1 : ℤ)) hH2)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ n - 1 : ℤ)) hH2) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ n - 1 : ℤ)) hH2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ n - 1 : ℤ)) hH2); parley_side)
  -- 2. def:prime p := 2^n − 1, from H2, 1
  have s2a : (2 ^ n - 1 : ℤ) > 1 := by first | linarith [(((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ n - 1 : ℤ).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side)]); parley_side)))).mp (by parley_side)).1] | (have h := (((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ n - 1 : ℤ).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side)]); parley_side)))).mp (by parley_side)).1; push_cast at h; linarith) | exact_mod_cast (((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ n - 1 : ℤ).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side)]); parley_side)))).mp (by parley_side)).1 | (have h := (((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ n - 1 : ℤ).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side)]); parley_side)))).mp (by parley_side)).1; parley_side)
  have s2b : ∀ c : ℕ, 0 < c → (c : ℤ) ∣ (2 ^ n - 1 : ℤ) → (c : ℤ) = 1 ∨ (c : ℤ) = 2 ^ n - 1 := by first | exact (((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ n - 1 : ℤ).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side)]); parley_side)))).mp (by parley_side)).2 | exact ((((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ n - 1 : ℤ).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side)]); parley_side)))).mp (by parley_side)).2).symm | simpa using (((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ n - 1 : ℤ).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side)]); parley_side)))).mp (by parley_side)).2 | exact_mod_cast (((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ n - 1 : ℤ).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side)]); parley_side)))).mp (by parley_side)).2 | (have h := (((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ n - 1 : ℤ).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ n - 1 : ℤ) by parley_side)]); parley_side)))).mp (by parley_side)).2; parley_side)
  -- 3. contradiction
  have s3 : (n : ℤ) > 1 := by
    by_contra hc_hS1
    have hS1 : ¬ (n : ℤ) > 1 := by parley_suppose hc_hS1
    -- 3.1. inequalities, from S1
    have s3_1 : (n : ℤ) ≤ 1 := by parley_order
    -- 3.2. inequalities, from H1
    have s3_2 : 1 ≤ (n : ℤ) := by parley_order
    -- 3.3. antisymmetry, from 3.1, 3.2
    have s3_3 : (n : ℤ) = 1 := by parley_side
    -- 3.4. substitute n = 1 (line 3.3) into line 2
    have s3_4 : (2 ^ 1 - 1 : ℤ) > 1 := by parley_subst_at s3_3 s2a
    -- 3.5. arithmetic
    have s3_5 : ¬ (2 ^ 1 - 1 : ℤ) > 1 := by parley_arith
    all_goals parley_side
  -- 4. proof
  have s4 : ∀ d : ℕ, 0 < d → (d : ℤ) ∣ (n : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = (n : ℤ) := by
    intro d hK1
    intro hK2
    by_contra hc_hS2
    have hS2 : ¬ ((d : ℤ) = 1 ∨ (d : ℤ) = (n : ℤ)) := by parley_suppose hc_hS2
    -- 4.1. mun:not-either P := d = 1, Q := d = n, from S2
    have s4_1a : (d : ℤ) ≠ 1 := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (n : ℤ)))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (n : ℤ)))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (n : ℤ)))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (n : ℤ)))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (n : ℤ)))).mp (by parley_side)).1; parley_side)
    have s4_1b : (d : ℤ) ≠ (n : ℤ) := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (n : ℤ)))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (n : ℤ)))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (n : ℤ)))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (n : ℤ)))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (n : ℤ)))).mp (by parley_side)).2; parley_side)
    -- 4.2. obtain e: def:divides, from K2
    obtain ⟨e, s4_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (d : ℤ)) (n := (n : ℤ)))).mp (by parley_side)
    -- 4.3. contradiction
    have s4_3 : 0 < e := by
      by_contra hc_hS3
      have hS3 : ¬ 0 < e := by parley_suppose hc_hS3
      -- 4.3.1. inequalities, from S3
      have s4_3_1 : e ≤ 0 := by parley_order
      -- 4.3.2. mun:multiply-le x := e, y := 0, c := d, from 4.3.1
      have r219_1 : (d : ℤ) > 0 := by parley_order
      have s4_3_2 : (d : ℤ) * e ≤ (d : ℤ) * 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := e) (y := (0 : ℤ)) (c := (d : ℤ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := e) (y := (0 : ℤ)) (c := (d : ℤ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := e) (y := (0 : ℤ)) (c := (d : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := e) (y := (0 : ℤ)) (c := (d : ℤ)) (by parley_side) (by parley_side)); parley_side)
      -- 4.3.3. substitute n = d·e (line 4.2) into line 4.3.2
      have s4_3_3 : (n : ℤ) ≤ (d : ℤ) * 0 := by parley_subst_at s4_2 s4_3_2
      -- 4.3.4. substitute
      have s4_3_4 : (n : ℤ) ≤ 0 := by
        have c1 : (d : ℤ) * 0 = 0 := by parley_ring
        have row1 : (n : ℤ) ≤ 0 := by parley_subst_at c1 s4_3_3
        exact row1
      -- 4.3.5. inequalities, from H1
      have s4_3_5 : ¬ (n : ℤ) ≤ 0 := by parley_side
      all_goals parley_side
    -- 4.4. mun:pos-int-nat m := e, from 4.3
    have s4_4 : 0 < e := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := e) s4_3) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := e) s4_3)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := e) s4_3) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := e) s4_3) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := e) s4_3); parley_side)
    lift e to ℕ using s4_4.le
    -- 4.5. contradiction
    have s4_5 : (e : ℤ) ≠ 1 := by
      by_contra hc_hS4
      have hS4 : (e : ℤ) = 1 := by parley_suppose hc_hS4
      -- 4.5.1. substitute e = 1 (S4) into line 4.2
      have s4_5_1 : (n : ℤ) = (d : ℤ) * 1 := by parley_subst_at hS4 s4_2
      -- 4.5.2. restate 4.5.1
      have s4_5_2 : (d : ℤ) = (n : ℤ) := by parley_side
      all_goals parley_side
    -- 4.6. mun:integer-step m := 1, n := e
    have r247_1 : 1 < (e : ℤ) := by parley_order
    have s4_6 : 1 + 1 ≤ (e : ℤ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (e : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (e : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (e : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (e : ℤ)) (by parley_side)); parley_side)
    -- 4.7. mun:integer-step m := 1, n := d
    have r251_1 : 1 < (d : ℤ) := by parley_order
    have s4_7 : 1 + 1 ≤ (d : ℤ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (d : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (d : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (d : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (d : ℤ)) (by parley_side)); parley_side)
    -- 4.8. obtain q: thm:power-multiple-quotient m := e, from 4.4
    obtain ⟨q, s4_8a, ⟨s4_8b, s4_8c⟩⟩ := (Parley.Proofs.Hammack.MersennePrimeExponent.PowerMultipleQuotient.power_multiple_quotient (d := d) (by parley_side) (m := e) (by parley_side))
    try lift q to ℕ using le_of_lt s4_8a
    -- 4.9. calculation
    have s4_9 : 2 ^ n - 1 = (2 ^ d - 1) * (q : ℤ) := by
      calc (2 ^ n - 1 : ℤ) = 2 ^ (d * e) - 1 := by parley_subst s4_2
        _ = (2 ^ d - 1) * (q : ℤ) := by parley_side
    -- 4.10. def:divides d := 2^d − 1, n := 2^n − 1, from 4.9
    have s4_10 : (2 ^ d - 1 : ℤ) ∣ (2 ^ n - 1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 ^ d - 1 : ℤ)) (n := (2 ^ n - 1 : ℤ)))).mpr ⟨(q : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 ^ d - 1 : ℤ)) (n := (2 ^ n - 1 : ℤ)))).mpr ⟨(q : ℤ), by parley_side⟩; parley_side)
    -- 4.11. thm:two-power-bound
    have s4_11 : 2 ^ d ≥ (d : ℤ) + 1 := by first | linarith [(Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound.two_power_bound (d := d) (by parley_side))] | (have h := (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound.two_power_bound (d := d) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound.two_power_bound (d := d) (by parley_side)) | (have h := (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound.two_power_bound (d := d) (by parley_side)); parley_side)
    -- 4.12. inequalities
    have s4_12 : 2 ^ d - 1 ≥ (d : ℤ) := by parley_order
    -- 4.13. transitivity, from 4.7, 4.12
    have s4_13 : (1 + 1 : ℤ) ≤ 2 ^ d - 1 := by parley_order
    -- 4.14. inequalities
    have s4_14 : (2 ^ d - 1 : ℤ) ≥ 2 := by parley_order
    -- 4.15. mun:pos-int-nat m := 2^d − 1
    have r283_1 : (0 : ℤ) < 2 ^ d - 1 := by parley_order
    have s4_15 : (0 : ℤ) < 2 ^ d - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (2 ^ d - 1 : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (2 ^ d - 1 : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (2 ^ d - 1 : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (2 ^ d - 1 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (2 ^ d - 1 : ℤ)) (by parley_side)); parley_side)
    -- 4.16. instantiate c := 2^d − 1 in line 2, from 4.15
    have s4_16 : (2 ^ d - 1 : ℤ) ∣ (2 ^ n - 1 : ℤ) → (2 ^ d - 1 : ℤ) = 1 ∨ (2 ^ d - 1 : ℤ) = 2 ^ n - 1 := by have h := (s2b (2 ^ d - 1 : ℤ).toNat (Int.lt_toNat.mpr (show ((0 : ℕ) : ℤ) < (2 ^ d - 1 : ℤ) by parley_side))); rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (2 ^ d - 1 : ℤ) by parley_side)] at h; exact h
    -- 4.17. mun:modus-ponens, from 4.10, 4.16
    have s4_17 : (2 ^ d - 1 : ℤ) = 1 ∨ (2 ^ d - 1 : ℤ) = 2 ^ n - 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 ^ d - 1 : ℤ) ∣ (2 ^ n - 1 : ℤ)) (Q := (2 ^ d - 1 : ℤ) = 1 ∨ (2 ^ d - 1 : ℤ) = 2 ^ n - 1) s4_16 s4_10) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 ^ d - 1 : ℤ) ∣ (2 ^ n - 1 : ℤ)) (Q := (2 ^ d - 1 : ℤ) = 1 ∨ (2 ^ d - 1 : ℤ) = 2 ^ n - 1) s4_16 s4_10)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 ^ d - 1 : ℤ) ∣ (2 ^ n - 1 : ℤ)) (Q := (2 ^ d - 1 : ℤ) = 1 ∨ (2 ^ d - 1 : ℤ) = 2 ^ n - 1) s4_16 s4_10) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 ^ d - 1 : ℤ) ∣ (2 ^ n - 1 : ℤ)) (Q := (2 ^ d - 1 : ℤ) = 1 ∨ (2 ^ d - 1 : ℤ) = 2 ^ n - 1) s4_16 s4_10) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 ^ d - 1 : ℤ) ∣ (2 ^ n - 1 : ℤ)) (Q := (2 ^ d - 1 : ℤ) = 1 ∨ (2 ^ d - 1 : ℤ) = 2 ^ n - 1) s4_16 s4_10); parley_side)
    -- 4.18. cases, from 4.17
    have s4_18 : (d : ℤ) = (n : ℤ) := by
      rcases s4_17 with hC1 | hC2
      · skip
        -- 4.18.1. inequalities, from 4.14
        have s4_18_1 : (2 ^ d - 1 : ℤ) > 1 := by parley_order
        -- 4.18.2. inequalities
        have s4_18_2 : (2 ^ d - 1 : ℤ) ≠ 1 := by parley_side
        all_goals parley_side
      · skip
        -- 4.18.3. inequalities
        have s4_18_3 : 2 ≤ (e : ℤ) := by parley_order
        -- 4.18.4. inequalities, from 4.8
        have s4_18_4 : (e : ℤ) ≤ (q : ℤ) := by parley_order
        -- 4.18.5. transitivity, from 4.18.3, 4.18.4
        have s4_18_5 : 2 ≤ (q : ℤ) := by parley_order
        -- 4.18.6. mun:multiply-le x := 2, y := q, c := 2^d − 1, from 4.18.5
        have r321_1 : (2 ^ d - 1 : ℤ) > 0 := by parley_order
        have s4_18_6 : (2 ^ d - 1) * 2 ≤ (2 ^ d - 1) * (q : ℤ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := (q : ℤ)) (c := (2 ^ d - 1 : ℤ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := (q : ℤ)) (c := (2 ^ d - 1 : ℤ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := (q : ℤ)) (c := (2 ^ d - 1 : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := (q : ℤ)) (c := (2 ^ d - 1 : ℤ)) (by parley_side) (by parley_side)); parley_side)
        -- 4.18.7. calculation
        have s4_18_7 : 2 ^ d - 1 = (2 ^ d - 1) * (q : ℤ) := by
          calc (2 ^ d - 1 : ℤ) = 2 ^ n - 1 := by parley_side
            _ = (2 ^ d - 1) * (q : ℤ) := by parley_side
        -- 4.18.8. inequalities, from 4.14
        have s4_18_8 : (0 : ℤ) < 2 ^ d - 1 := by parley_order
        -- 4.18.9. inequalities
        have s4_18_9 : (2 ^ d - 1 : ℤ) < (2 ^ d - 1) * 2 := by parley_order
        -- 4.18.10. transitivity, from 4.18.9, 4.18.6
        have s4_18_10 : 2 ^ d - 1 < (2 ^ d - 1) * (q : ℤ) := by parley_order
        -- 4.18.11. inequalities
        have s4_18_11 : 2 ^ d - 1 ≠ (2 ^ d - 1) * (q : ℤ) := by parley_side
        all_goals parley_side
    all_goals parley_side
  -- 5. def:prime p := n, from 3, 4
  have s5 : Nat.Prime n := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_prime (p := n) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := n) (by parley_side))).mpr (by parley_side); parley_side)
  all_goals exact s5

end Parley.Proofs.Hammack.MersennePrimeExponent.PrimeExponent

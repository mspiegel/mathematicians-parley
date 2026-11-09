module

public import AlgebraTactics
public import ArithTactics
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Hammack.MersennePrimeExponent.PowerMultipleQuotient
public import Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound

/-! Written from proofs/hammack/mersenne-prime-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MersennePrimeExponent.PrimeExponent

set_option maxHeartbeats 1000000 in
theorem prime_exponent (n : ℤ) (hH1 : 0 < n) (hH2 : Nat.Prime (2 ^ n.toNat - 1 : ℤ).toNat) :
    Nat.Prime n.toNat := by
  -- 1. mun:prime-nat p := 2^n − 1, from H2
  have s1 : (0 : ℤ) < 2 ^ n.toNat - 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := (2 ^ n.toNat - 1 : ℤ)) hH2)
  -- 2. def:prime p := 2^n − 1, from H2, 1
  have s2a : (2 ^ n.toNat - 1 : ℤ) > 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ n.toNat - 1 : ℤ)) (by parley_side))).mp hH2).1
  have s2b : ∀ c : ℤ, 0 < c → c ∣ (2 ^ n.toNat - 1 : ℤ) → c = 1 ∨ c = 2 ^ n.toNat - 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := (2 ^ n.toNat - 1 : ℤ)) (by parley_side))).mp hH2).2
  -- 3. contradiction
  have s3 : n > 1 := by
    by_contra hS1
    -- 3.1. inequalities, from S1
    have s3_1 : n ≤ 1 := by parley_order
    -- 3.2. inequalities, from H1
    have s3_2 : 1 ≤ n := by parley_order
    -- 3.3. antisymmetry, from 3.1, 3.2
    have s3_3 : n = 1 := by parley_side
    -- 3.4. substitute n = 1 (line 3.3) into line 2
    have s3_4 : (2 ^ 1 - 1 : ℤ) > 1 := by parley_subst_at s3_3 s2a
    -- 3.5. arithmetic
    have s3_5 : ¬ (2 ^ 1 - 1 : ℤ) > 1 := by parley_arith
    exact s3_5 s3_4
  -- 4. proof
  have s4 : ∀ d : ℤ, 0 < d → d ∣ n → d = 1 ∨ d = n := by
    intro d hK1
    intro hK2
    by_contra hS2
    -- 4.1. mun:not-either P := d = 1, Q := d = n, from S2
    have s4_1a : d ≠ 1 := by
      have hI : d ≠ 1 := by parley_instance ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = n))).mp hS2).1)
      exact hI
    have s4_1b : d ≠ n := by
      have hI : d ≠ n := by parley_instance ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = n))).mp hS2).2)
      exact hI
    -- 4.2. obtain e: def:divides, from K2
    obtain ⟨e, s4_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := d) (n := n))).mp hK2
    -- 4.3. contradiction
    have s4_3 : 0 < e := by
      by_contra hS3
      -- 4.3.1. inequalities, from S3
      have s4_3_1 : e ≤ 0 := by parley_order
      -- 4.3.2. mun:multiply-le x := e, y := 0, c := d, from 4.3.1
      have r219_1 : d > 0 := by parley_order
      have s4_3_2 : d * e ≤ d * 0 := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := e) (y := (0 : ℤ)) (c := d) (by parley_side) (by parley_side))
      -- 4.3.3. substitute n = d·e (line 4.2) into line 4.3.2
      have s4_3_3 : n ≤ d * 0 := by parley_subst_at s4_2 s4_3_2
      -- 4.3.4. substitute
      have s4_3_4 : n ≤ 0 := by
        have c1 : d * 0 = 0 := by parley_ring
        have row1 : n ≤ 0 := by parley_subst_at c1 s4_3_3
        exact row1
      -- 4.3.5. inequalities, from H1
      have s4_3_5 : ¬ n ≤ 0 := by parley_side
      exact s4_3_5 s4_3_4
    -- 4.4. mun:pos-int-nat m := e, from 4.3
    have s4_4 : 0 < e := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := e) s4_3)
    -- 4.5. contradiction
    have s4_5 : e ≠ 1 := by
      intro hS4
      -- 4.5.1. substitute e = 1 (S4) into line 4.2
      have s4_5_1 : n = d * 1 := by parley_subst_at hS4 s4_2
      -- 4.5.2. restate 4.5.1
      have s4_5_2 : d = n := by parley_side
      exact s4_1b s4_5_2
    -- 4.6. mun:integer-step m := 1, n := e
    have r247_1 : 1 < e := by parley_order
    have s4_6 : 1 + 1 ≤ e := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := e) r247_1)
    -- 4.7. mun:integer-step m := 1, n := d
    have r251_1 : 1 < d := by parley_order
    have s4_7 : 1 + 1 ≤ d := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := d) r251_1)
    -- 4.8. obtain q: thm:power-multiple-quotient m := e, from 4.4
    obtain ⟨q, s4_8a, ⟨s4_8b, s4_8c⟩⟩ := (Parley.Proofs.Hammack.MersennePrimeExponent.PowerMultipleQuotient.power_multiple_quotient (d := d) (by parley_side) (m := e) (by parley_side))
    -- 4.9. calculation
    have s4_9 : 2 ^ n.toNat - 1 = (2 ^ d.toNat - 1) * q := by
      try qify
      calc (2 ^ n.toNat - 1 : ℚ) = 2 ^ (d * e) - 1 := by
            have s4_2_w : (n : ℚ) = (d : ℚ) * (e : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s4_2; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst s4_2_w | parley_subst s4_2
        _ = (2 ^ d.toNat - 1) * (q : ℚ) := by first | parley_side | parley_line_toNat s4_8a | parley_line_toNat s4_8b | parley_line_toNat s4_8c
    -- 4.10. def:divides d := 2^d − 1, n := 2^n − 1, from 4.9
    have s4_10 : (2 ^ d.toNat - 1 : ℤ) ∣ (2 ^ n.toNat - 1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 ^ d.toNat - 1 : ℤ)) (n := (2 ^ n.toNat - 1 : ℤ)))).mpr ⟨q, s4_9⟩
    -- 4.11. thm:two-power-bound
    have s4_11 : 2 ^ d.toNat ≥ d + 1 := by exact (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound.two_power_bound (d := d) (by parley_side))
    -- 4.12. inequalities
    have s4_12 : 2 ^ d.toNat - 1 ≥ d := by parley_order
    -- 4.13. transitivity, from 4.7, 4.12
    have s4_13 : (1 + 1 : ℤ) ≤ 2 ^ d.toNat - 1 := by parley_order
    -- 4.14. inequalities
    have s4_14 : (2 ^ d.toNat - 1 : ℤ) ≥ 2 := by parley_order
    -- 4.15. mun:pos-int-nat m := 2^d − 1
    have r283_1 : (0 : ℤ) < 2 ^ d.toNat - 1 := by parley_order
    have s4_15 : (0 : ℤ) < 2 ^ d.toNat - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (2 ^ d.toNat - 1 : ℤ)) r283_1)
    -- 4.16. instantiate c := 2^d − 1 in line 2, from 4.15
    have s4_16 : (2 ^ d.toNat - 1 : ℤ) ∣ (2 ^ n.toNat - 1 : ℤ) → (2 ^ d.toNat - 1 : ℤ) = 1 ∨ (2 ^ d.toNat - 1 : ℤ) = 2 ^ n.toNat - 1 := by exact (s2b (2 ^ d.toNat - 1 : ℤ) (by parley_side))
    -- 4.17. mun:modus-ponens, from 4.10, 4.16
    have s4_17 : (2 ^ d.toNat - 1 : ℤ) = 1 ∨ (2 ^ d.toNat - 1 : ℤ) = 2 ^ n.toNat - 1 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 ^ d.toNat - 1 : ℤ) ∣ (2 ^ n.toNat - 1 : ℤ)) (Q := (2 ^ d.toNat - 1 : ℤ) = 1 ∨ (2 ^ d.toNat - 1 : ℤ) = 2 ^ n.toNat - 1) s4_16 s4_10)
    -- 4.18. cases, from 4.17
    have s4_18 : d = n := by
      rcases s4_17 with hC1 | hC2
      · skip
        -- 4.18.1. inequalities, from 4.14
        have s4_18_1 : (2 ^ d.toNat - 1 : ℤ) > 1 := by parley_order
        -- 4.18.2. inequalities
        have s4_18_2 : (2 ^ d.toNat - 1 : ℤ) ≠ 1 := by parley_side
        exact absurd hC1 s4_18_2
      · skip
        -- 4.18.3. inequalities
        have s4_18_3 : 2 ≤ e := by parley_order
        -- 4.18.4. inequalities, from 4.8
        have s4_18_4 : e ≤ q := by parley_order
        -- 4.18.5. transitivity, from 4.18.3, 4.18.4
        have s4_18_5 : 2 ≤ q := by parley_order
        -- 4.18.6. mun:multiply-le x := 2, y := q, c := 2^d − 1, from 4.18.5
        have r321_1 : (2 ^ d.toNat - 1 : ℤ) > 0 := by parley_order
        have s4_18_6 : (2 ^ d.toNat - 1) * 2 ≤ (2 ^ d.toNat - 1) * q := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := q) (c := (2 ^ d.toNat - 1 : ℤ)) (by parley_side) (by parley_side))
        -- 4.18.7. calculation
        have s4_18_7 : 2 ^ d.toNat - 1 = (2 ^ d.toNat - 1) * q := by
          calc (2 ^ d.toNat - 1 : ℤ) = 2 ^ n.toNat - 1 := by parley_side
            _ = (2 ^ d.toNat - 1) * q := by exact s4_9
        -- 4.18.8. inequalities, from 4.14
        have s4_18_8 : (0 : ℤ) < 2 ^ d.toNat - 1 := by parley_order
        -- 4.18.9. inequalities
        have s4_18_9 : (2 ^ d.toNat - 1 : ℤ) < (2 ^ d.toNat - 1) * 2 := by parley_order
        -- 4.18.10. transitivity, from 4.18.9, 4.18.6
        have s4_18_10 : 2 ^ d.toNat - 1 < (2 ^ d.toNat - 1) * q := by parley_order
        -- 4.18.11. inequalities
        have s4_18_11 : 2 ^ d.toNat - 1 ≠ (2 ^ d.toNat - 1) * q := by parley_side
        exact absurd s4_18_7 s4_18_11
    exact s4_1b s4_18
  -- 5. def:prime p := n, from 3, 4
  exact ((Parley.Items.Stdlib.Divisibility.def_prime (p := n) (by parley_side))).mpr (by parley_side)

end Parley.Proofs.Hammack.MersennePrimeExponent.PrimeExponent

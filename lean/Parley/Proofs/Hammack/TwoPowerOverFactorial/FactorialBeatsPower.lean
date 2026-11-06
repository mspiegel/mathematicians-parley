module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import OrderTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/two-power-over-factorial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower

set_option maxHeartbeats 400000 in
theorem factorial_beats_power (n : ℤ) (hH1 : 0 < n) :
    n * 2 ^ n.toNat ≤ 4 * (LeanBridges.Counting.factorial n : ℤ) := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → 2 ^ k.toNat ≤ 2 * (LeanBridges.Counting.factorial k : ℤ) ∧ k * 2 ^ k.toNat ≤ 4 * (LeanBridges.Counting.factorial k : ℤ) := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : 2 ^ 1 ≤ 2 * (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by parley_arith
      -- 1.2. arithmetic
      have s1_2 : 1 * 2 ^ 1 ≤ 4 * (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by parley_arith
      -- 1.3. join 1.1, 1.2
      have s1_3 : 2 ^ 1 ≤ 2 * (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) ∧ 1 * 2 ^ 1 ≤ 4 * (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by parley_side
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.4. mun:factorial-nat n := k
      have s1_4 : 0 < (LeanBridges.Counting.factorial k : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) (by parley_side)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) (by parley_side)); parley_side)
      -- 1.5. inequalities, from 1.4
      have s1_5 : (LeanBridges.Counting.factorial k : ℤ) > 0 := by parley_order
      -- 1.6. def:factorial n := k
      have s1_6 : (LeanBridges.Counting.factorial (k + 1) : ℤ) = (LeanBridges.Counting.factorial k : ℤ) * (k + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); parley_side)
      -- 1.7. mun:exponent-step a := 2, m := k
      have s1_7 : (2 ^ (k + 1).toNat : ℤ) = 2 ^ k.toNat * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); parley_side)
      -- 1.8. inequalities
      have s1_8 : 2 ^ k.toNat * 2 ≤ 2 * (LeanBridges.Counting.factorial k : ℤ) * 2 := by parley_order
      -- 1.9. inequalities, from K
      have s1_9 : k ≥ 1 := by parley_order
      -- 1.10. inequalities
      have s1_10 : k + 1 ≥ 2 := by parley_order
      -- 1.11. inequalities
      have s1_11 : 2 * (LeanBridges.Counting.factorial k : ℤ) > 0 := by parley_order
      -- 1.12. mun:multiply-le x := 2, y := k + 1, c := 2·k!, from 1.10, 1.11
      have s1_12 : 2 * (LeanBridges.Counting.factorial k : ℤ) * 2 ≤ 2 * (LeanBridges.Counting.factorial k : ℤ) * (k + 1) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := k + 1) (c := 2 * (LeanBridges.Counting.factorial k : ℤ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := k + 1) (c := 2 * (LeanBridges.Counting.factorial k : ℤ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := k + 1) (c := 2 * (LeanBridges.Counting.factorial k : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := k + 1) (c := 2 * (LeanBridges.Counting.factorial k : ℤ)) (by parley_side) (by parley_side)); parley_side)
      -- 1.13. algebra, from 1.6
      have s1_13 : 2 * (LeanBridges.Counting.factorial k : ℤ) * (k + 1) = 2 * (LeanBridges.Counting.factorial (k + 1) : ℤ) := by linear_combination (norm := parley_norm) (-2) * s1_6
      -- 1.14. transitivity, from 1.7, 1.8, 1.12, 1.13
      have s1_14 : 2 ^ (k + 1).toNat ≤ 2 * (LeanBridges.Counting.factorial (k + 1) : ℤ) := by parley_order
      -- 1.15. calculation
      have r78_1 : k + 1 > 0 := by parley_order
      have s1_15 : (k + 1) * 2 ^ (k + 1).toNat ≤ 4 * (LeanBridges.Counting.factorial (k + 1) : ℤ) := by
        calc (k + 1) * 2 ^ (k + 1).toNat = (k + 1) * (2 ^ k.toNat * 2) := by linear_combination (norm := parley_norm) (k + 1) * s1_7
          _ ≤ (k + 1) * (2 * (LeanBridges.Counting.factorial k : ℤ) * 2) := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 ^ k.toNat * 2 : ℤ)) (y := 2 * (LeanBridges.Counting.factorial k : ℤ) * 2) (c := k + 1) (by parley_side) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 ^ k.toNat * 2 : ℤ)) (y := 2 * (LeanBridges.Counting.factorial k : ℤ) * 2) (c := k + 1) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 ^ k.toNat * 2 : ℤ)) (y := 2 * (LeanBridges.Counting.factorial k : ℤ) * 2) (c := k + 1) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 ^ k.toNat * 2 : ℤ)) (y := 2 * (LeanBridges.Counting.factorial k : ℤ) * 2) (c := k + 1) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 ^ k.toNat * 2 : ℤ)) (y := 2 * (LeanBridges.Counting.factorial k : ℤ) * 2) (c := k + 1) (by parley_side) (by parley_side)); parley_side)
          _ = 4 * (LeanBridges.Counting.factorial (k + 1) : ℤ) := by linear_combination (norm := parley_norm) (-4) * s1_6
      -- 1.16. join 1.14, 1.15
      have s1_16 : 2 ^ (k + 1).toNat ≤ 2 * (LeanBridges.Counting.factorial (k + 1) : ℤ) ∧ (k + 1) * 2 ^ (k + 1).toNat ≤ 4 * (LeanBridges.Counting.factorial (k + 1) : ℤ) := by parley_side
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : 2 ^ n.toNat ≤ 2 * (LeanBridges.Counting.factorial n : ℤ) ∧ n * 2 ^ n.toNat ≤ 4 * (LeanBridges.Counting.factorial n : ℤ) := by first | exact (s1 n (by parley_side)) | exact ((s1 n (by parley_side))).symm | simpa using (s1 n (by parley_side)) | exact_mod_cast (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 n (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_side)
  -- 3. restate 2
  have s3 : n * 2 ^ n.toNat ≤ 4 * (LeanBridges.Counting.factorial n : ℤ) := by parley_side
  all_goals exact s3

end Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower

module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/two-power-over-factorial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower

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
      have s1_3 : 2 ^ 1 ≤ 2 * (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) ∧ 1 * 2 ^ 1 ≤ 4 * (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := ⟨s1_1, s1_2⟩
      exact ⟨by simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using (s1_3).1, by simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using (s1_3).2⟩
    | succ k hK hIH =>
      -- 1.4. mun:factorial-nat n := k
      have s1_4 : 0 < (LeanBridges.Counting.factorial k : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) (le_of_lt (lt_of_lt_of_le zero_lt_one hK)))
      -- 1.5. inequalities, from 1.4
      have s1_5 : (LeanBridges.Counting.factorial k : ℤ) > 0 := by linarith only [s1_4]
      -- 1.6. def:factorial n := k
      have s1_6 : (LeanBridges.Counting.factorial (k + 1) : ℤ) = (LeanBridges.Counting.factorial k : ℤ) * (k + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (le_of_lt (lt_of_lt_of_le zero_lt_one hK)))
      -- 1.7. mun:exponent-step a := 2, m := k
      have s1_7 : (2 ^ (k + 1).toNat : ℤ) = 2 ^ k.toNat * 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (le_of_lt (lt_of_lt_of_le zero_lt_one hK)))
      -- 1.8. inequalities
      have s1_8 : 2 ^ k.toNat * 2 ≤ 2 * (LeanBridges.Counting.factorial k : ℤ) * 2 := by linarith only [hIH.1]
      -- 1.9. inequalities, from K
      have s1_9 : k ≥ 1 := by linarith only [lt_of_lt_of_le zero_lt_one hK]
      -- 1.10. inequalities
      have s1_10 : k + 1 ≥ 2 := by linarith only [s1_9]
      -- 1.11. inequalities
      have s1_11 : 2 * (LeanBridges.Counting.factorial k : ℤ) > 0 := by linarith only [s1_5]
      -- 1.12. mun:multiply-le x := 2, y := k + 1, c := 2·k!, from 1.10, 1.11
      have s1_12 : 2 * (LeanBridges.Counting.factorial k : ℤ) * 2 ≤ 2 * (LeanBridges.Counting.factorial k : ℤ) * (k + 1) := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := k + 1) (c := 2 * (LeanBridges.Counting.factorial k : ℤ)) s1_10 s1_11)
      -- 1.13. algebra, from 1.6
      have s1_13 : 2 * (LeanBridges.Counting.factorial k : ℤ) * (k + 1) = 2 * (LeanBridges.Counting.factorial (k + 1) : ℤ) := by linear_combination (norm := parley_norm) (-2) * s1_6
      -- 1.14. transitivity, from 1.7, 1.8, 1.12, 1.13
      have s1_14 : 2 ^ (k + 1).toNat ≤ 2 * (LeanBridges.Counting.factorial (k + 1) : ℤ) := by exact LE.le.trans_eq (le_trans (Eq.trans_le s1_7 s1_8) s1_12) s1_13
      -- 1.15. calculation
      have r78_1 : k + 1 > 0 := by linarith only [lt_of_lt_of_le zero_lt_one hK]
      have s1_15 : (k + 1) * 2 ^ (k + 1).toNat ≤ 4 * (LeanBridges.Counting.factorial (k + 1) : ℤ) := by
        calc (k + 1) * 2 ^ (k + 1).toNat = (k + 1) * (2 ^ k.toNat * 2) := by linear_combination (norm := parley_norm) (k + 1) * s1_7
          _ ≤ (k + 1) * (2 * (LeanBridges.Counting.factorial k : ℤ) * 2) := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 ^ k.toNat * 2 : ℤ)) (y := 2 * (LeanBridges.Counting.factorial k : ℤ) * 2) (c := k + 1) s1_8 r78_1)
          _ = 4 * (LeanBridges.Counting.factorial (k + 1) : ℤ) := by linear_combination (norm := parley_norm) (-4) * s1_6
      -- 1.16. join 1.14, 1.15
      have s1_16 : 2 ^ (k + 1).toNat ≤ 2 * (LeanBridges.Counting.factorial (k + 1) : ℤ) ∧ (k + 1) * 2 ^ (k + 1).toNat ≤ 4 * (LeanBridges.Counting.factorial (k + 1) : ℤ) := ⟨s1_14, s1_15⟩
      exact ⟨(s1_16).1, (s1_16).2⟩
  -- 2. instantiate k := n in line 1
  have s2 : 2 ^ n.toNat ≤ 2 * (LeanBridges.Counting.factorial n : ℤ) ∧ n * 2 ^ n.toNat ≤ 4 * (LeanBridges.Counting.factorial n : ℤ) := by exact (s1 n hH1)
  -- 3. restate 2
  exact s2.2

end Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower

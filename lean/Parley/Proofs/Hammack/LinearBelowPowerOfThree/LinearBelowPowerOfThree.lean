module

public import ArithTactics
public import Functions
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
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/linear-below-power-of-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LinearBelowPowerOfThree.LinearBelowPowerOfThree

theorem linear_below_power_of_three (n : ℤ) (hH1 : 0 < n) :
    2 * n + 1 ≤ 3 ^ n.toNat := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → 2 * k + 1 ≤ 3 ^ k.toNat := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (2 * 1 + 1 : ℤ) ≤ 3 ^ 1 := by parley_arith
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s1_1
    | succ k hK hIH =>
      -- 1.2. mun:exponent-step a := 3
      have s1_2 : (3 ^ (k + 1).toNat : ℤ) = 3 ^ k.toNat * 3 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (le_of_lt (lt_of_lt_of_le zero_lt_one hK)))
      -- 1.3. inequalities
      have s1_3 : 6 * k + 3 ≤ 3 ^ k.toNat * 3 := by linarith only [hIH]
      -- 1.4. inequalities, from K
      have s1_4 : 0 < k := by linarith only [lt_of_lt_of_le zero_lt_one hK]
      -- 1.5. inequalities
      have s1_5 : 2 * (k + 1) + 1 ≤ 6 * k + 3 := by linarith only [s1_4]
      -- 1.6. transitivity, from 1.5, 1.3, 1.2
      exact LE.le.trans_eq (le_trans s1_5 s1_3) s1_2.symm
  -- 2. instantiate k := n in line 1
  exact (s1 n hH1)

end Parley.Proofs.Hammack.LinearBelowPowerOfThree.LinearBelowPowerOfThree

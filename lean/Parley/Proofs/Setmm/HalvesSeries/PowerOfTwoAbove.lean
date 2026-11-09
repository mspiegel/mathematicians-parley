module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/halves-series.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.HalvesSeries.PowerOfTwoAbove

theorem power_of_two_above (n : ℤ) (hH1 : 0 < n) :
    n ≤ 2 ^ n.toNat := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → k ≤ 2 ^ k.toNat := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (1 : ℤ) ≤ 2 ^ 1 := by parley_arith
      simpa using s1_1
    | succ k hK hIH =>
      -- 1.2. mun:power-nat a := 2, m := k
      have s1_2 : (0 : ℤ) < 2 ^ k.toNat := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by parley_side) (m := k) (by parley_side))
      -- 1.3. inequalities, from IH, 1.2
      have s1_3 : k + 1 ≤ 2 ^ k.toNat + 2 ^ k.toNat := by parley_order
      -- 1.4. calculation
      calc k + 1 ≤ 2 ^ k.toNat + 2 ^ k.toNat := by parley_side
        _ = 2 ^ k.toNat * 2 := by parley_ring
        _ = 2 ^ (k + 1).toNat := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)).symm
  -- 2. instantiate k := n in line 1
  exact (s1 n (by parley_side))

end Parley.Proofs.Setmm.HalvesSeries.PowerOfTwoAbove

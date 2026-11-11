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

/-! Written from proofs/hammack/product-of-one-minus-halves.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour

theorem power_of_two_at_least_four (m : ℤ) (hH1 : 0 < m) :
    (2 ^ (m + 1).toNat : ℤ) ≥ 4 := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → (2 ^ (k + 1).toNat : ℤ) ≥ 4 := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      parley_arith
    | succ k hK hIH =>
      -- 1.2. mun:power-nat a := 2, m := k + 1
      have s1_2 : (0 : ℤ) < 2 ^ (k + 1).toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by parley_side) (m := k + 1) (by parley_side))
      -- 1.3. inequalities, from 1.2
      have s1_3 : (2 ^ (k + 1).toNat : ℤ) ≥ 0 := by parley_order
      -- 1.4. inequalities, from IH, 1.3
      have s1_4 : (2 ^ (k + 1).toNat + 2 ^ (k + 1).toNat : ℤ) ≥ 4 := by parley_order
      -- 1.5. calculation
      calc (2 ^ (k + 1 + 1).toNat : ℤ) = 2 ^ (k + 1).toNat * 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side))
        _ = 2 ^ (k + 1).toNat + 2 ^ (k + 1).toNat := by parley_ring
        _ ≥ 4 := by exact s1_4
  -- 2. instantiate k := m in line 1
  exact (s1 m hH1)

end Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour

module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd
public import Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound

/-! Written from proofs/hammack/mersenne-prime-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MersennePrimeExponent.PowerMultipleQuotient

set_option maxHeartbeats 400000 in
theorem power_multiple_quotient (d : ℤ) (hH1 : 0 < d) (m : ℤ) (hH2 : 0 < m) :
    (∃ q : ℤ, 0 < q ∧ (2 ^ (d * m).toNat - 1 = (2 ^ d.toNat - 1) * q ∧ q ≥ m)) := by
  -- 1. induction on j starting at 1
  have s1 : ∀ j : ℤ, 0 < j → (∃ q : ℤ, 0 < q ∧ (2 ^ (d * j).toNat - 1 = (2 ^ d.toNat - 1) * q ∧ q ≥ j)) := by
    intro j h_j
    replace h_j : 1 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (1 : ℤ) ≥ 1 := by parley_arith
      -- 1.2. exhibit, from 1.1
      exact ⟨(1 : ℤ), by parley_side, ⟨by parley_side, s1_1⟩⟩
    | succ j hK hIH =>
      -- 1.3. obtain q from IH
      obtain ⟨q, s1_3a, ⟨s1_3b, s1_3c⟩⟩ := hIH
      -- 1.4. algebra
      have s1_4 : d * (j + 1) = d * j + d := by parley_ring
      -- 1.5. calculation
      have s1_5 : (2 ^ (d * (j + 1)).toNat : ℤ) = 2 ^ (d * j).toNat * 2 ^ d.toNat := by
        calc (2 ^ (d * (j + 1)).toNat : ℤ) = 2 ^ (d * j + d).toNat := by parley_subst s1_4
          _ = 2 ^ (d * j).toNat * 2 ^ d.toNat := by exact (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd.two_power_add (a := d * j) (by parley_side) (b := d) (by parley_side))
      -- 1.6. calculation
      have s1_6 : 2 ^ (d * (j + 1)).toNat - 1 = (2 ^ d.toNat - 1) * (2 ^ d.toNat * q + 1) := by
        calc (2 ^ (d * (j + 1)).toNat - 1 : ℤ) = 2 ^ (d * j).toNat * 2 ^ d.toNat - 1 := by parley_subst s1_5
          _ = 2 ^ d.toNat * (2 ^ (d * j).toNat - 1) + (2 ^ d.toNat - 1) := by parley_ring
          _ = 2 ^ d.toNat * ((2 ^ d.toNat - 1) * q) + (2 ^ d.toNat - 1) := by parley_subst s1_3b
          _ = (2 ^ d.toNat - 1) * (2 ^ d.toNat * q + 1) := by parley_ring
      -- 1.7. thm:two-power-bound
      have s1_7 : 2 ^ d.toNat ≥ d + 1 := by exact (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound.two_power_bound (d := d) (by parley_side))
      -- 1.8. inequalities, from H1
      have s1_8 : d + 1 ≥ 1 := by parley_order
      -- 1.9. transitivity, from 1.7, 1.8
      have s1_9 : (2 ^ d.toNat : ℤ) ≥ 1 := by parley_order
      -- 1.10. mun:multiply-le x := 1, y := 2^d, c := q, from 1.9
      have r134_1 : q > 0 := by parley_order
      have s1_10 : q * 1 ≤ q * 2 ^ d.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := (2 ^ d.toNat : ℤ)) (c := q) (by parley_side) (by parley_side))
      -- 1.11. algebra
      have s1_11 : q * 2 ^ d.toNat = 2 ^ d.toNat * q := by parley_ring
      -- 1.12. inequalities
      have s1_12 : q ≤ q * 2 ^ d.toNat := by parley_order
      -- 1.13. inequalities, from 1.3
      have s1_13 : j ≤ q := by parley_order
      -- 1.14. transitivity, from 1.13, 1.12, 1.11
      have s1_14 : j ≤ 2 ^ d.toNat * q := by parley_order
      -- 1.15. inequalities
      have s1_15 : 2 ^ d.toNat * q + 1 ≥ j + 1 := by parley_order
      -- 1.16. exhibit, from 1.6, 1.15
      exact ⟨2 ^ d.toNat * q + 1, by parley_side, ⟨s1_6, s1_15⟩⟩
  -- 2. instantiate j := m in line 1
  exact (s1 m (by parley_side))

end Parley.Proofs.Hammack.MersennePrimeExponent.PowerMultipleQuotient

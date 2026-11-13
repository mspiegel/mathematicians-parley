module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
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
      exact ⟨(1 : ℤ), by norm_num, ⟨by simp only [mul_one], by norm_num⟩⟩
    | succ j hK hIH =>
      -- 1.3. obtain q from IH
      obtain ⟨q, s1_3a, ⟨s1_3b, s1_3c⟩⟩ := hIH
      -- 1.4. algebra
      have s1_4 : d * (j + 1) = d * j + d := by parley_ring
      -- 1.5. calculation
      have s1_5 : (2 ^ (d * (j + 1)).toNat : ℤ) = 2 ^ (d * j).toNat * 2 ^ d.toNat := by
        calc (2 ^ (d * (j + 1)).toNat : ℤ) = 2 ^ (d * j + d).toNat := by (have h := congrArg (fun t : ℤ => 2 ^ t.toNat) s1_4; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 2 ^ (d * j).toNat * 2 ^ d.toNat := by exact (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd.two_power_add (a := d * j) (mul_nonneg (le_of_lt hH1) (le_of_lt (lt_of_lt_of_le zero_lt_one hK))) (b := d) (le_of_lt hH1))
      -- 1.6. calculation
      have s1_6 : 2 ^ (d * (j + 1)).toNat - 1 = (2 ^ d.toNat - 1) * (2 ^ d.toNat * q + 1) := by
        calc (2 ^ (d * (j + 1)).toNat - 1 : ℤ) = 2 ^ (d * j).toNat * 2 ^ d.toNat - 1 := by (have h := congrArg (fun t : ℤ => t - 1) s1_5; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 2 ^ d.toNat * (2 ^ (d * j).toNat - 1) + (2 ^ d.toNat - 1) := by parley_ring
          _ = 2 ^ d.toNat * ((2 ^ d.toNat - 1) * q) + (2 ^ d.toNat - 1) := by (have h := congrArg (fun t : ℤ => 2 ^ d.toNat * t + (2 ^ d.toNat - 1)) s1_3b; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = (2 ^ d.toNat - 1) * (2 ^ d.toNat * q + 1) := by parley_ring
      -- 1.7. thm:two-power-bound
      have s1_7 : 2 ^ d.toNat ≥ d + 1 := by exact (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound.two_power_bound (d := d) hH1)
      -- 1.8. inequalities, from H1
      have s1_8 : d + 1 ≥ 1 := by linarith only [hH1]
      -- 1.9. transitivity, from 1.7, 1.8
      have s1_9 : (2 ^ d.toNat : ℤ) ≥ 1 := by exact le_trans s1_8 s1_7
      -- 1.10. mun:multiply-le x := 1, y := 2^d, c := q, from 1.9
      have r134_1 : q > 0 := by linarith only [s1_3a]
      have s1_10 : q * 1 ≤ q * 2 ^ d.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := (2 ^ d.toNat : ℤ)) (c := q) s1_9 r134_1)
      -- 1.11. algebra
      have s1_11 : q * 2 ^ d.toNat = 2 ^ d.toNat * q := by parley_ring
      -- 1.12. inequalities
      have s1_12 : q ≤ q * 2 ^ d.toNat := by linarith only [s1_10]
      -- 1.13. inequalities, from 1.3
      have s1_13 : j ≤ q := by linarith only [s1_3c]
      -- 1.14. transitivity, from 1.13, 1.12, 1.11
      have s1_14 : j ≤ 2 ^ d.toNat * q := by exact LE.le.trans_eq (le_trans s1_13 s1_12) s1_11
      -- 1.15. inequalities
      have s1_15 : 2 ^ d.toNat * q + 1 ≥ j + 1 := by linarith only [s1_14]
      -- 1.16. exhibit, from 1.6, 1.15
      exact ⟨2 ^ d.toNat * q + 1, add_pos (mul_pos (pow_pos (by norm_num) _) (s1_3a)) (by norm_num), ⟨s1_6, s1_15⟩⟩
  -- 2. instantiate j := m in line 1
  exact (s1 m hH2)

end Parley.Proofs.Hammack.MersennePrimeExponent.PowerMultipleQuotient

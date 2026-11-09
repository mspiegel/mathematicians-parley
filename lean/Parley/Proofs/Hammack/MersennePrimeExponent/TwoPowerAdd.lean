module

public import AlgebraTactics
public import ArithTactics
public import Functions
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

/-! Written from proofs/hammack/mersenne-prime-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd

theorem two_power_add (a : ℤ) (hH1 : 0 ≤ a) (b : ℤ) (hH2 : 0 ≤ b) :
    (2 ^ (a + b).toNat : ℤ) = 2 ^ a.toNat * 2 ^ b.toNat := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (2 ^ (a + k).toNat : ℤ) = 2 ^ a.toNat * 2 ^ k.toNat := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (2 ^ 0 : ℤ) = 1 := by parley_arith
      -- 1.2. substitute 2^0 = 1 (line 1.1)
      have s1_2 : (2 ^ a.toNat : ℤ) = 2 ^ a.toNat * 2 ^ 0 := by parley_subst s1_1
      simpa only [add_zero, Int.reduceToNat] using s1_2
    | succ k hK hIH =>
      -- 1.3. algebra
      have s1_3 : a + (k + 1) = a + k + 1 := by parley_ring
      -- 1.4. mun:exponent-step a := 2, m := k
      have s1_4 : (2 ^ (k + 1).toNat : ℤ) = 2 ^ k.toNat * 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side))
      -- 1.5. calculation
      calc (2 ^ (a + (k + 1)).toNat : ℤ) = 2 ^ (a + k + 1).toNat := by parley_subst s1_3
        _ = 2 ^ (a + k).toNat * 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side))
        _ = 2 ^ a.toNat * 2 ^ k.toNat * 2 := by parley_subst hIH
        _ = 2 ^ a.toNat * (2 ^ k.toNat * 2) := by parley_ring
        _ = 2 ^ a.toNat * 2 ^ (k + 1).toNat := by parley_subst s1_4
  -- 2. instantiate k := b in line 1
  exact (s1 b (by parley_side))

end Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd

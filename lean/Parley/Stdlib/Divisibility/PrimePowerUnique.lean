module

public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.PrimePowerUnique

theorem prime_power_unique (p : ℤ) (hH1 : 0 < p) (hH2 : Nat.Prime p.toNat) (a : ℤ) (hH3 : 0 ≤ a) (a' : ℤ) (hH4 : 0 ≤ a') (m : ℤ) (m' : ℤ) (hH7 : (Int.gcd m p : ℤ) = 1) (hH8 : (Int.gcd m' p : ℤ) = 1) (hH9 : p ^ a.toNat * m = p ^ a'.toNat * m') :
    a = a' := by
  -- 1. mun:prime-power-not-less, from H2, H7, H9
  have s1 : ¬ a < a' := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) hH1 hH2 (a := a) hH3 (a' := a') hH4 (m := m) (m' := m') hH7 hH9)
  -- 2. restate H9
  have s2 : p ^ a'.toNat * m' = p ^ a.toNat * m := by exact hH9.symm
  -- 3. mun:prime-power-not-less a := a′, a′ := a, m := m′, m′ := m, from H2, H8, 2
  have s3 : ¬ a' < a := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) hH1 hH2 (a := a') hH4 (a' := a) hH3 (m := m') (m' := m) hH8 s2)
  -- 4. inequalities, from 1
  have s4 : a' ≤ a := by linarith only [s1]
  -- 5. inequalities, from 3
  have s5 : a ≤ a' := by linarith only [s3]
  -- 6. antisymmetry, from 4, 5
  exact le_antisymm s5 s4

end Parley.Stdlib.Divisibility.PrimePowerUnique

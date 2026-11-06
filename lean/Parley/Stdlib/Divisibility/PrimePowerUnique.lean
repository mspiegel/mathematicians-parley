module

public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Parley.Items.Stdlib.Divisibility

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.PrimePowerUnique

theorem prime_power_unique (p : ℤ) (hH1 : 0 < p) (hH2 : Nat.Prime p.toNat) (a : ℤ) (hH3 : 0 ≤ a) (a' : ℤ) (hH4 : 0 ≤ a') (m : ℤ) (m' : ℤ) (hH7 : (Int.gcd m p : ℤ) = 1) (hH8 : (Int.gcd m' p : ℤ) = 1) (hH9 : p ^ a.toNat * m = p ^ a'.toNat * m') :
    a = a' := by
  -- 1. mun:prime-power-not-less, from H2, H7, H9
  have s1 : ¬ a < a' := by first | exact (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) hH2 (a := a) (by parley_side) (a' := a') (by parley_side) (m := m) (m' := m') hH7 hH9) | exact ((Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) hH2 (a := a) (by parley_side) (a' := a') (by parley_side) (m := m) (m' := m') hH7 hH9)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) hH2 (a := a) (by parley_side) (a' := a') (by parley_side) (m := m) (m' := m') hH7 hH9) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) hH2 (a := a) (by parley_side) (a' := a') (by parley_side) (m := m) (m' := m') hH7 hH9) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) hH2 (a := a) (by parley_side) (a' := a') (by parley_side) (m := m) (m' := m') hH7 hH9); parley_side)
  -- 2. restate H9
  have s2 : p ^ a'.toNat * m' = p ^ a.toNat * m := by parley_side
  -- 3. mun:prime-power-not-less a := a′, a′ := a, m := m′, m′ := m, from H2, H8, 2
  have s3 : ¬ a' < a := by first | exact (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) hH2 (a := a') (by parley_side) (a' := a) (by parley_side) (m := m') (m' := m) hH8 s2) | exact ((Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) hH2 (a := a') (by parley_side) (a' := a) (by parley_side) (m := m') (m' := m) hH8 s2)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) hH2 (a := a') (by parley_side) (a' := a) (by parley_side) (m := m') (m' := m) hH8 s2) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) hH2 (a := a') (by parley_side) (a' := a) (by parley_side) (m := m') (m' := m) hH8 s2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) hH2 (a := a') (by parley_side) (a' := a) (by parley_side) (m := m') (m' := m) hH8 s2); parley_side)
  -- 4. inequalities, from 1
  have s4 : a' ≤ a := by parley_order
  -- 5. inequalities, from 3
  have s5 : a ≤ a' := by parley_order
  -- 6. antisymmetry, from 4, 5
  have s6 : a = a' := by parley_side
  all_goals exact s6

end Parley.Stdlib.Divisibility.PrimePowerUnique

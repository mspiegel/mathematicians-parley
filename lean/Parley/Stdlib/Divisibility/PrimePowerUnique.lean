module

public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.PrimePowerUnique

theorem prime_power_unique (p : ℕ) (hH1 : 0 < p) (hH2 : Nat.Prime p) (a : ℕ) (a' : ℕ) (m : ℤ) (m' : ℤ) (hH7 : (Int.gcd m (p : ℤ) : ℤ) = 1) (hH8 : (Int.gcd m' (p : ℤ) : ℤ) = 1) (hH9 : (p : ℤ) ^ a * m = (p : ℤ) ^ a' * m') :
    (a : ℤ) = (a' : ℤ) := by
  -- 1. mun:prime-power-not-less, from H2, H7, H9
  have s1 : ¬ (a : ℤ) < (a' : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) (by parley_side) (a := a) (a' := a') (m := m) (m' := m') (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) (by parley_side) (a := a) (a' := a') (m := m) (m' := m') (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) (by parley_side) (a := a) (a' := a') (m := m) (m' := m') (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) (by parley_side) (a := a) (a' := a') (m := m) (m' := m') (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) (by parley_side) (a := a) (a' := a') (m := m) (m' := m') (by parley_side) (by parley_side)); parley_side)
  -- 2. restate H9
  have s2 : (p : ℤ) ^ a' * m' = (p : ℤ) ^ a * m := by parley_side
  -- 3. mun:prime-power-not-less a := a′, a′ := a, m := m′, m′ := m, from H2, H8, 2
  have s3 : ¬ (a' : ℤ) < (a : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) (by parley_side) (a := a') (a' := a) (m := m') (m' := m) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) (by parley_side) (a := a') (a' := a) (m := m') (m' := m) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) (by parley_side) (a := a') (a' := a) (m := m') (m' := m) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) (by parley_side) (a := a') (a' := a) (m := m') (m' := m) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_power_not_less (p := p) (by parley_side) (by parley_side) (a := a') (a' := a) (m := m') (m' := m) (by parley_side) (by parley_side)); parley_side)
  -- 4. inequalities, from 1
  have s4 : (a' : ℤ) ≤ (a : ℤ) := by parley_order
  -- 5. inequalities, from 3
  have s5 : (a : ℤ) ≤ (a' : ℤ) := by parley_order
  -- 6. antisymmetry, from 4, 5
  have s6 : (a : ℤ) = (a' : ℤ) := by parley_side
  all_goals exact s6

end Parley.Stdlib.Divisibility.PrimePowerUnique

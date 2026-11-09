module

public import ArithTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.PrimePowersUnique

set_option maxHeartbeats 600000 in
theorem prime_powers_unique (a : ℤ) (hH1 : 0 ≤ a) (b : ℤ) (hH2 : 0 ≤ b) (c : ℤ) (hH3 : 0 ≤ c) (a' : ℤ) (hH4 : 0 ≤ a') (b' : ℤ) (hH5 : 0 ≤ b') (c' : ℤ) (hH6 : 0 ≤ c') (hH7 : (2 ^ a.toNat * 3 ^ b.toNat * 5 ^ c.toNat : ℤ) = 2 ^ a'.toNat * 3 ^ b'.toNat * 5 ^ c'.toNat) :
    a = a' ∧ b = b' ∧ c = c' := by
  -- 1. mun:two-prime
  have s1 : Nat.Prime (2 : ℤ).toNat := by exact Parley.Items.Stdlib.Divisibility.mun_two_prime
  -- 2. inspection
  have s2 : Nat.Prime (3 : ℤ).toNat := by parley_side
  -- 3. inspection
  have s3 : Nat.Prime (5 : ℤ).toNat := by parley_side
  -- 4. mun:prime-coprime p := 3, a := 2, from 2
  have r518_1 : ¬ (3 : ℤ) ∣ (2 : ℤ) := by parley_arith
  have s4 : (Int.gcd (3 : ℤ) (2 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s2 (a := (2 : ℤ)) r518_1)
  -- 5. mun:prime-coprime p := 5, a := 2, from 3
  have r522_1 : ¬ (5 : ℤ) ∣ (2 : ℤ) := by parley_arith
  have s5 : (Int.gcd (5 : ℤ) (2 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (5 : ℤ)) (by parley_side) s3 (a := (2 : ℤ)) r522_1)
  -- 6. mun:prime-coprime p := 2, a := 3, from 1
  have r526_1 : ¬ (2 : ℤ) ∣ (3 : ℤ) := by parley_arith
  have s6 : (Int.gcd (2 : ℤ) (3 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (2 : ℤ)) (by parley_side) s1 (a := (3 : ℤ)) r526_1)
  -- 7. mun:prime-coprime p := 5, a := 3, from 3
  have r530_1 : ¬ (5 : ℤ) ∣ (3 : ℤ) := by parley_arith
  have s7 : (Int.gcd (5 : ℤ) (3 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (5 : ℤ)) (by parley_side) s3 (a := (3 : ℤ)) r530_1)
  -- 8. mun:prime-coprime p := 2, a := 5, from 1
  have r534_1 : ¬ (2 : ℤ) ∣ (5 : ℤ) := by parley_arith
  have s8 : (Int.gcd (2 : ℤ) (5 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (2 : ℤ)) (by parley_side) s1 (a := (5 : ℤ)) r534_1)
  -- 9. mun:prime-coprime p := 3, a := 5, from 2
  have r538_1 : ¬ (3 : ℤ) ∣ (5 : ℤ) := by parley_arith
  have s9 : (Int.gcd (3 : ℤ) (5 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s2 (a := (5 : ℤ)) r538_1)
  -- 10. mun:coprime-product x := 3^b, y := 5^c, n := 2
  have r542_1 : (Int.gcd (3 ^ b.toNat : ℤ) (2 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (3 : ℤ)) (b := (2 : ℤ)) (k := b) (by parley_side) s4)
  have r542_2 : (Int.gcd (5 ^ c.toNat : ℤ) (2 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (5 : ℤ)) (b := (2 : ℤ)) (k := c) (by parley_side) s5)
  have s10 : (Int.gcd (3 ^ b.toNat * 5 ^ c.toNat : ℤ) (2 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_product (x := (3 ^ b.toNat : ℤ)) (y := (5 ^ c.toNat : ℤ)) (n := (2 : ℤ)) (by parley_side) r542_1 r542_2)
  -- 11. mun:coprime-product x := 3^b′, y := 5^c′, n := 2
  have r547_1 : (Int.gcd (3 ^ b'.toNat : ℤ) (2 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (3 : ℤ)) (b := (2 : ℤ)) (k := b') (by parley_side) s4)
  have r547_2 : (Int.gcd (5 ^ c'.toNat : ℤ) (2 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (5 : ℤ)) (b := (2 : ℤ)) (k := c') (by parley_side) s5)
  have s11 : (Int.gcd (3 ^ b'.toNat * 5 ^ c'.toNat : ℤ) (2 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_product (x := (3 ^ b'.toNat : ℤ)) (y := (5 ^ c'.toNat : ℤ)) (n := (2 : ℤ)) (by parley_side) r547_1 r547_2)
  -- 12. algebra, from H7
  have s12 : (2 ^ a.toNat * (3 ^ b.toNat * 5 ^ c.toNat) : ℤ) = 2 ^ a'.toNat * (3 ^ b'.toNat * 5 ^ c'.toNat) := by linear_combination (norm := parley_norm) hH7
  -- 13. mun:prime-power-unique p := 2, m := 3^b·5^c, m′ := 3^b′·5^c′, from 1, 10, 11, 12
  have s13 : a = a' := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_power_unique (p := (2 : ℤ)) (by parley_side) s1 (a := a) (by parley_side) (a' := a') (by parley_side) (m := (3 ^ b.toNat * 5 ^ c.toNat : ℤ)) (m' := (3 ^ b'.toNat * 5 ^ c'.toNat : ℤ)) s10 s11 s12)
  -- 14. mun:coprime-product x := 2^a, y := 5^c, n := 3
  have r559_1 : (Int.gcd (2 ^ a.toNat : ℤ) (3 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (2 : ℤ)) (b := (3 : ℤ)) (k := a) (by parley_side) s6)
  have r559_2 : (Int.gcd (5 ^ c.toNat : ℤ) (3 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (5 : ℤ)) (b := (3 : ℤ)) (k := c) (by parley_side) s7)
  have s14 : (Int.gcd (2 ^ a.toNat * 5 ^ c.toNat : ℤ) (3 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_product (x := (2 ^ a.toNat : ℤ)) (y := (5 ^ c.toNat : ℤ)) (n := (3 : ℤ)) (by parley_side) r559_1 r559_2)
  -- 15. mun:coprime-product x := 2^a′, y := 5^c′, n := 3
  have r564_1 : (Int.gcd (2 ^ a'.toNat : ℤ) (3 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (2 : ℤ)) (b := (3 : ℤ)) (k := a') (by parley_side) s6)
  have r564_2 : (Int.gcd (5 ^ c'.toNat : ℤ) (3 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (5 : ℤ)) (b := (3 : ℤ)) (k := c') (by parley_side) s7)
  have s15 : (Int.gcd (2 ^ a'.toNat * 5 ^ c'.toNat : ℤ) (3 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_product (x := (2 ^ a'.toNat : ℤ)) (y := (5 ^ c'.toNat : ℤ)) (n := (3 : ℤ)) (by parley_side) r564_1 r564_2)
  -- 16. algebra, from H7
  have s16 : (3 ^ b.toNat * (2 ^ a.toNat * 5 ^ c.toNat) : ℤ) = 3 ^ b'.toNat * (2 ^ a'.toNat * 5 ^ c'.toNat) := by linear_combination (norm := parley_norm) hH7
  -- 17. mun:prime-power-unique p := 3, a := b, a′ := b′, m := 2^a·5^c, m′ := 2^a′·5^c′, from 2, 14, 15, 16
  have s17 : b = b' := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_power_unique (p := (3 : ℤ)) (by parley_side) s2 (a := b) (by parley_side) (a' := b') (by parley_side) (m := (2 ^ a.toNat * 5 ^ c.toNat : ℤ)) (m' := (2 ^ a'.toNat * 5 ^ c'.toNat : ℤ)) s14 s15 s16)
  -- 18. mun:coprime-product x := 2^a, y := 3^b, n := 5
  have r576_1 : (Int.gcd (2 ^ a.toNat : ℤ) (5 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (2 : ℤ)) (b := (5 : ℤ)) (k := a) (by parley_side) s8)
  have r576_2 : (Int.gcd (3 ^ b.toNat : ℤ) (5 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (3 : ℤ)) (b := (5 : ℤ)) (k := b) (by parley_side) s9)
  have s18 : (Int.gcd (2 ^ a.toNat * 3 ^ b.toNat : ℤ) (5 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_product (x := (2 ^ a.toNat : ℤ)) (y := (3 ^ b.toNat : ℤ)) (n := (5 : ℤ)) (by parley_side) r576_1 r576_2)
  -- 19. mun:coprime-product x := 2^a′, y := 3^b′, n := 5
  have r581_1 : (Int.gcd (2 ^ a'.toNat : ℤ) (5 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (2 : ℤ)) (b := (5 : ℤ)) (k := a') (by parley_side) s8)
  have r581_2 : (Int.gcd (3 ^ b'.toNat : ℤ) (5 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_power (a := (3 : ℤ)) (b := (5 : ℤ)) (k := b') (by parley_side) s9)
  have s19 : (Int.gcd (2 ^ a'.toNat * 3 ^ b'.toNat : ℤ) (5 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_product (x := (2 ^ a'.toNat : ℤ)) (y := (3 ^ b'.toNat : ℤ)) (n := (5 : ℤ)) (by parley_side) r581_1 r581_2)
  -- 20. algebra, from H7
  have s20 : (5 ^ c.toNat * (2 ^ a.toNat * 3 ^ b.toNat) : ℤ) = 5 ^ c'.toNat * (2 ^ a'.toNat * 3 ^ b'.toNat) := by linear_combination (norm := parley_norm) hH7
  -- 21. mun:prime-power-unique p := 5, a := c, a′ := c′, m := 2^a·3^b, m′ := 2^a′·3^b′, from 3, 18, 19, 20
  have s21 : c = c' := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_power_unique (p := (5 : ℤ)) (by parley_side) s3 (a := c) (by parley_side) (a' := c') (by parley_side) (m := (2 ^ a.toNat * 3 ^ b.toNat : ℤ)) (m' := (2 ^ a'.toNat * 3 ^ b'.toNat : ℤ)) s18 s19 s20)
  -- 22. join 13, 17, 21
  have s22a : a = a' := by parley_side
  have s22b : b = b' := by parley_side
  have s22c : c = c' := by parley_side
  exact ⟨s22a, s22b, s22c⟩

end Parley.Stdlib.Divisibility.PrimePowersUnique

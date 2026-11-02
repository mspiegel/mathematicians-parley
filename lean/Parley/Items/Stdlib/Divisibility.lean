module

public import Divisibility
public import Tactics

/-! Written from corpus/stdlib/divisibility.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Divisibility

theorem def_divides (d : ℤ) (n : ℤ) :
    d ∣ n ↔ (∃ k : ℤ, n = d * k) :=
  Iff.rfl

theorem def_even (n : ℤ) :
    Even n ↔ (∃ k : ℤ, n = 2 * k) :=
  even_iff_exists_two_mul

theorem def_odd (n : ℤ) :
    Odd n ↔ (∃ k : ℤ, n = 2 * k + 1) :=
  Iff.rfl

theorem mun_even_or_odd (n : ℤ) :
    Even n ∨ Odd n :=
  Int.even_or_odd n

theorem mun_not_both (n : ℤ) (h2 : Even n) :
    ¬ Odd n :=
  Int.not_odd_iff_even.mpr h2

theorem mun_odd_not_even (n : ℤ) (h2 : Odd n) :
    ¬ Even n :=
  Int.not_even_iff_odd.mpr h2

theorem mun_even_product (a : ℤ) (h2 : Even a) (x : ℤ) :
    Even (a * x) :=
  h2.mul_right x

theorem mun_even_product_factor (a : ℤ) (b : ℤ) :
    Even (a * b) ↔ Even a ∨ Even b :=
  Int.even_mul

theorem thm_prime_divides_product (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) (m : ℤ) (n : ℤ) :
    (p : ℤ) ∣ m * n ↔ (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n :=
  LeanBridges.Divisibility.prime_divides_product p h1 h2 m n

theorem thm_divides_gcd (d : ℤ) (a : ℤ) (b : ℤ) (h4 : d ∣ a) (h5 : d ∣ b) :
    d ∣ (Int.gcd a b : ℤ) :=
  Int.dvd_coe_gcd h4 h5

theorem def_prime (p : ℕ) (h1 : 0 < p) :
    Nat.Prime p ↔ 1 < (p : ℤ) ∧ (∀ d : ℕ, 0 < d → (d : ℤ) ∣ (p : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = (p : ℤ)) :=
  LeanBridges.Divisibility.prime p h1

theorem def_gcd_1 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    0 < (Int.gcd (a : ℤ) (b : ℤ) : ℤ) :=
  LeanBridges.Divisibility.gcd_1 a h1 b h2

theorem def_gcd_2 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    (Int.gcd (a : ℤ) (b : ℤ) : ℤ) ∣ (a : ℤ) :=
  Int.gcd_dvd_left a b

theorem def_gcd_3 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    (Int.gcd (a : ℤ) (b : ℤ) : ℤ) ∣ (b : ℤ) :=
  Int.gcd_dvd_right a b

theorem def_gcd_4 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    ∀ e : ℕ, 0 < e → (e : ℤ) ∣ (a : ℤ) ∧ (e : ℤ) ∣ (b : ℤ) → (e : ℤ) ≤ (Int.gcd (a : ℤ) (b : ℤ) : ℤ) :=
  LeanBridges.Divisibility.gcd_4 a h1 b h2

theorem def_lcm_1 (a : ℤ) (b : ℤ) :
    0 ≤ (Int.lcm a b : ℤ) :=
  LeanBridges.Divisibility.lcm_1 a b

theorem def_lcm_2 (a : ℤ) (b : ℤ) :
    a ∣ (Int.lcm a b : ℤ) :=
  Int.dvd_lcm_left a b

theorem def_lcm_3 (a : ℤ) (b : ℤ) :
    b ∣ (Int.lcm a b : ℤ) :=
  Int.dvd_lcm_right a b

theorem def_lcm_4 (a : ℤ) (b : ℤ) :
    ∀ k : ℤ, a ∣ k ∧ b ∣ k → (Int.lcm a b : ℤ) ∣ k :=
  LeanBridges.Divisibility.lcm_4 a b

theorem thm_prime_factor (m : ℕ) (h1 : 0 < m) (h2 : 1 < (m : ℤ)) :
    ∃ p : ℕ, 0 < p ∧ (Nat.Prime p ∧ (p : ℤ) ∣ (m : ℤ)) :=
  LeanBridges.Divisibility.prime_factor m h1 h2

theorem mun_divides_sum (d : ℤ) (a : ℤ) (b : ℤ) (h4 : d ∣ a) (h5 : d ∣ b) :
    d ∣ a + b :=
  dvd_add h4 h5

theorem mun_divides_difference (d : ℤ) (a : ℤ) (b : ℤ) (h4 : d ∣ a) (h5 : d ∣ b) :
    d ∣ a - b :=
  dvd_sub h4 h5

theorem mun_divides_one (d : ℕ) (h1 : 0 < d) (h2 : (d : ℤ) ∣ (1 : ℤ)) :
    (d : ℤ) = 1 :=
  LeanBridges.Divisibility.divides_one d h1 h2

theorem mun_divides_combination (e : ℤ) (a : ℤ) (b : ℤ) (x : ℤ) (y : ℤ) (h6 : e ∣ a) (h7 : e ∣ b) :
    e ∣ a * x + b * y :=
  dvd_add (Dvd.dvd.mul_right h6 x) (Dvd.dvd.mul_right h7 y)

theorem mun_divides_le (e : ℕ) (h1 : 0 < e) (m : ℕ) (h2 : 0 < m) (h3 : (e : ℤ) ∣ (m : ℤ)) :
    (e : ℤ) ≤ (m : ℤ) :=
  Int.le_of_dvd (by omega) h3

theorem def_congruent_mod (n : ℤ) (a : ℤ) (b : ℤ) :
    a ≡ b [ZMOD n] ↔ n ∣ a - b :=
  Int.modEq_comm.trans Int.modEq_iff_dvd

theorem mun_divides_multiple (e : ℤ) (a : ℤ) (x : ℤ) (h4 : e ∣ a) :
    e ∣ a * x :=
  Dvd.dvd.mul_right h4 x

theorem mun_gcd_integer_1 (a : ℤ) (b : ℤ) :
    0 ≤ (Int.gcd a b : ℤ) :=
  LeanBridges.Divisibility.gcd_integer_1 a b

theorem mun_gcd_integer_2 (a : ℤ) (b : ℤ) :
    (Int.gcd a b : ℤ) ∣ a :=
  Int.gcd_dvd_left a b

theorem mun_gcd_integer_3 (a : ℤ) (b : ℤ) :
    (Int.gcd a b : ℤ) ∣ b :=
  Int.gcd_dvd_right a b

theorem mun_gcd_commutes (a : ℤ) (b : ℤ) :
    (Int.gcd a b : ℤ) = (Int.gcd b a : ℤ) :=
  LeanBridges.Divisibility.gcd_commutes a b

theorem mun_gcd_one (a : ℤ) :
    (Int.gcd a (1 : ℤ) : ℤ) = 1 :=
  LeanBridges.Divisibility.gcd_one a

theorem mun_gcd_zero (n : ℕ) :
    (Int.gcd (n : ℤ) (0 : ℤ) : ℤ) = (n : ℤ) :=
  LeanBridges.Divisibility.gcd_zero n

theorem thm_gcd_mod (a : ℤ) (b : ℕ) (h2 : 0 < b) :
    (Int.gcd (a % (b : ℤ)) (b : ℤ) : ℤ) = (Int.gcd a (b : ℤ) : ℤ) :=
  LeanBridges.Divisibility.gcd_mod a b h2

theorem mun_mod_natural (a : ℤ) (b : ℕ) (h2 : 0 < b) :
    0 ≤ a % (b : ℤ) :=
  Int.emod_nonneg a (by omega)

theorem mun_mod_less (a : ℤ) (b : ℕ) (h2 : 0 < b) :
    a % (b : ℤ) < (b : ℤ) :=
  Int.emod_lt_of_pos a (by omega)

theorem mun_mod_remainder (a : ℤ) (m : ℕ) (h2 : 0 < m) (r : ℕ) (h4 : (r : ℤ) < (m : ℤ)) :
    a % (m : ℤ) = (r : ℤ) ↔ (∃ q : ℤ, q * (m : ℤ) + (r : ℤ) = a) :=
  LeanBridges.Divisibility.mod_remainder a m h2 r h4

theorem mun_mod_multiple (r : ℤ) (m : ℕ) (h2 : 0 < m) (q : ℤ) :
    (q * (m : ℤ) + r) % (m : ℤ) = r % (m : ℤ) :=
  LeanBridges.Divisibility.mod_multiple r m h2 q

theorem mun_zero_divides (n : ℤ) :
    (0 : ℤ) ∣ n ↔ n = 0 :=
  zero_dvd_iff

theorem mun_divides_self (n : ℤ) :
    n ∣ n :=
  dvd_refl n

theorem mun_prime_coprime (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) (a : ℤ) (h4 : ¬ (p : ℤ) ∣ a) :
    (Int.gcd (p : ℤ) a : ℤ) = 1 :=
  LeanBridges.Divisibility.prime_coprime p h1 h2 a h4

theorem mun_mod_equal_congruent (x : ℤ) (y : ℤ) (n : ℕ) (h3 : 0 < n) (h4 : x % (n : ℤ) = y % (n : ℤ)) :
    x ≡ y [ZMOD (n : ℤ)] :=
  h4

theorem mun_divides_quotient (n : ℕ) (h1 : 0 < n) (d : ℕ) (h2 : 0 < d) :
    (d : ℤ) ∣ (n : ℤ) ↔ (∃ m : ℕ, 0 < m ∧ (m : ℚ) = (n : ℚ) / (d : ℚ)) :=
  LeanBridges.Divisibility.divides_quotient n h1 d h2

end Parley.Items.Stdlib.Divisibility

module

public import Parley.Library

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

theorem mun_even_product_factor (a : ℤ) (b : ℤ) :
    Even (a * b) ↔ Even a ∨ Even b :=
  Int.even_mul

theorem mun_divides_sum (d : ℤ) (a : ℤ) (b : ℤ) (h4 : d ∣ a) (h5 : d ∣ b) :
    d ∣ a + b :=
  dvd_add h4 h5

theorem mun_divides_difference (d : ℤ) (a : ℤ) (b : ℤ) (h4 : d ∣ a) (h5 : d ∣ b) :
    d ∣ a - b :=
  dvd_sub h4 h5

theorem mun_divides_one (d : ℕ) (h1 : 0 < d) (h2 : (d : ℤ) ∣ (1 : ℤ)) :
    (d : ℤ) = 1 :=
  by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h2

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

theorem mun_mod_multiple (r : ℤ) (m : ℕ) (h2 : 0 < m) (q : ℤ) :
    (q * (m : ℤ) + r) % (m : ℤ) = r % (m : ℤ) :=
  by rw [add_comm, Int.add_mul_emod_self_right]

theorem mun_divides_self (n : ℤ) :
    n ∣ n :=
  dvd_refl n

end Parley.Items.Stdlib.Divisibility

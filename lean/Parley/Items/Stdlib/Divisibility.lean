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

theorem mun_divides_sum (d : ℤ) (a : ℤ) (b : ℤ) (h4 : d ∣ a) (h5 : d ∣ b) :
    d ∣ a + b :=
  dvd_add h4 h5

theorem mun_divides_difference (d : ℤ) (a : ℤ) (b : ℤ) (h4 : d ∣ a) (h5 : d ∣ b) :
    d ∣ a - b :=
  dvd_sub h4 h5

theorem def_congruent_mod (n : ℤ) (a : ℤ) (b : ℤ) :
    a ≡ b [ZMOD n] ↔ n ∣ a - b :=
  Int.modEq_comm.trans Int.modEq_iff_dvd

theorem mun_divides_multiple (e : ℤ) (a : ℤ) (x : ℤ) (h4 : e ∣ a) :
    e ∣ a * x :=
  Dvd.dvd.mul_right h4 x

theorem mun_divides_self (n : ℤ) :
    n ∣ n :=
  dvd_refl n

end Parley.Items.Stdlib.Divisibility

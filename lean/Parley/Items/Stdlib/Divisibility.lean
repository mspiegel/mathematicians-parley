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

end Parley.Items.Stdlib.Divisibility

module

public import Parley.Library

/-! Written from corpus/stdlib/numbers.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Numbers

theorem mun_exponent_step {K : Type*} [CommRing K] (a : K) (m : ℕ) :
    a ^ (m + 1) = a ^ m * a :=
  pow_succ a m

theorem mun_exponent_sum {K : Type*} [CommRing K] (a : K) (m : ℕ) (n : ℕ) :
    a ^ (m + n) = a ^ m * a ^ n :=
  pow_add a m n

theorem mun_nonneg_or_neg {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) :
    0 ≤ x ∨ x < 0 :=
  le_or_gt 0 x

theorem mun_square_nonneg {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) :
    0 ≤ x ^ 2 :=
  sq_nonneg x

end Parley.Items.Stdlib.Numbers

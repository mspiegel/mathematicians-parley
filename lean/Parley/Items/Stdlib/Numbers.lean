module

public import Parley.Library

/-! Written from corpus/stdlib/numbers.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Numbers

theorem mun_floor_integer (x : ℝ) :
    True :=
  trivial

theorem mun_exponent_step {K : Type*} [CommRing K] (a : K) (m : ℕ) :
    a ^ (m + 1) = a ^ m * a :=
  pow_succ a m

theorem mun_exponent_sum {K : Type*} [CommRing K] (a : K) (m : ℕ) (n : ℕ) :
    a ^ (m + n) = a ^ m * a ^ n :=
  pow_add a m n

theorem axi_trichotomy {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) :
    (x < 0 ∨ x = 0) ∨ 0 < x :=
  or_assoc.mpr (lt_trichotomy x 0)

theorem mun_nonneg_or_neg {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) :
    0 ≤ x ∨ x < 0 :=
  le_or_gt 0 x

theorem mun_square_nonneg {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) :
    0 ≤ x ^ 2 :=
  sq_nonneg x

theorem mun_multiply_le {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) (y : K) (c : K) (h4 : x ≤ y) (h5 : 0 < c) :
    c * x ≤ c * y :=
  mul_le_mul_of_nonneg_left h4 h5.le

theorem mun_product_nonneg {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) (y : K) (h3 : 0 ≤ x) (h4 : 0 ≤ y) :
    0 ≤ x * y :=
  mul_nonneg h3 h4

end Parley.Items.Stdlib.Numbers

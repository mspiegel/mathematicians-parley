module

public import Parley.Library

/-! Written from corpus/stdlib/numbers.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Numbers

theorem mun_pos_int_nat (m : ℤ) (h2 : 0 < m) :
    0 < m :=
  h2

theorem mun_integer_step (m : ℤ) (n : ℤ) (h3 : m < n) :
    m + 1 ≤ n :=
  by omega

theorem mun_floor_integer (x : ℝ) :
    True :=
  trivial

theorem mun_floor_below (x : ℝ) :
    (⌊x⌋ : ℝ) ≤ x :=
  Int.floor_le x

theorem mun_floor_above (x : ℝ) :
    x < (⌊x⌋ : ℝ) + 1 :=
  Int.lt_floor_add_one x

theorem mun_exponent_step {K : Type*} [CommRing K] [IsDomain K] (a : K) (m : ℕ) :
    a ^ (m + 1) = a ^ m * a :=
  pow_succ a m

theorem mun_exponent_sum {K : Type*} [CommRing K] [IsDomain K] (a : K) (m : ℕ) (n : ℕ) :
    a ^ (m + n) = a ^ m * a ^ n :=
  pow_add a m n

theorem mun_power_nat (a : ℕ) (h1 : 0 < a) (m : ℕ) :
    0 < (a : ℤ) ^ m :=
  by positivity

theorem axi_trichotomy {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) :
    (x < 0 ∨ x = 0) ∨ 0 < x :=
  or_assoc.mpr (lt_trichotomy x 0)

theorem mun_nonneg_or_neg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) :
    0 ≤ x ∨ x < 0 :=
  le_or_gt 0 x

theorem mun_square_nonneg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) :
    0 ≤ x ^ 2 :=
  sq_nonneg x

theorem mun_multiply_le {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) (y : K) (c : K) (h4 : x ≤ y) (h5 : 0 < c) :
    c * x ≤ c * y :=
  mul_le_mul_of_nonneg_left h4 h5.le

theorem mun_square_positive {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) (h2 : x ≠ 0) :
    0 < x ^ 2 :=
  lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 h2))

theorem mun_square_le {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) (y : K) (h3 : 0 ≤ x) (h4 : 0 ≤ y) :
    x ≤ y ↔ x ^ 2 ≤ y ^ 2 :=
  ⟨fun h => by nlinarith, fun h => by nlinarith⟩

theorem mun_product_nonneg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) (y : K) (h3 : 0 ≤ x) (h4 : 0 ≤ y) :
    0 ≤ x * y :=
  mul_nonneg h3 h4

theorem mun_zero_product {K : Type*} [CommRing K] [IsDomain K] (x : K) (y : K) :
    x * y = 0 ↔ x = 0 ∨ y = 0 :=
  mul_eq_zero

theorem mun_less_scaled {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) (y : K) (c : K) (h4 : 0 < c) :
    x < y ↔ c * x < c * y :=
  ⟨fun h => by nlinarith, fun h => by nlinarith⟩

theorem mun_multiply_cancel {K : Type*} [CommRing K] [IsDomain K] (a : K) (b : K) (c : K) (h4 : a * c = b * c) (h5 : c ≠ 0) :
    a = b :=
  mul_right_cancel₀ h5 h4

theorem thm_triangle_inequality {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] (a : K) (b : K) :
    |a + b| ≤ |a| + |b| :=
  abs_add_le a b

end Parley.Items.Stdlib.Numbers

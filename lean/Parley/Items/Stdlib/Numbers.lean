module

public import Numbers
public import Tactics

/-! Written from corpus/stdlib/numbers.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Numbers

theorem def_rational {K : Type*} [Field K] [CharZero K] (x : K) :
    (∃ m : ℚ, (m : K) = x) ↔ (∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ x = (p : K) / (q : K)) :=
  LeanBridges.Numbers.rational x

theorem def_irrational (x : ℝ) :
    Irrational x ↔ True ∧ ¬ (∃ m : ℚ, (m : ℝ) = x) :=
  LeanBridges.Numbers.irrational x

theorem def_sqrt_1 (x : ℝ) (h2 : 0 ≤ x) :
    True :=
  trivial

theorem def_sqrt_2 (x : ℝ) (h2 : 0 ≤ x) :
    0 ≤ Real.sqrt x :=
  Real.sqrt_nonneg x

theorem def_sqrt_3 (x : ℝ) (h2 : 0 ≤ x) :
    Real.sqrt x ^ 2 = x :=
  Real.sq_sqrt h2

theorem mun_int_closure_1 (a : ℤ) :
    True :=
  trivial

theorem mun_int_closure_2 (a : ℤ) (b : ℤ) :
    True :=
  trivial

theorem mun_int_closure_3 (a : ℤ) (b : ℤ) :
    True :=
  trivial

theorem mun_int_closure_4 (a : ℤ) (b : ℤ) :
    True :=
  trivial

theorem mun_nat_closure_1 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    0 < (a : ℤ) + (b : ℤ) :=
  LeanBridges.Numbers.nat_closure_1 a h1 b h2

theorem mun_nat_closure_2 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    0 < (a : ℤ) * (b : ℤ) :=
  LeanBridges.Numbers.nat_closure_2 a h1 b h2

theorem mun_real_closure_1 {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (x : K) (y : K) :
    True :=
  trivial

theorem mun_real_closure_2 {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (x : K) (y : K) :
    True :=
  trivial

theorem mun_nat0_successor (k : ℕ) :
    0 < (k : ℤ) + 1 :=
  LeanBridges.Numbers.nat0_successor k

theorem mun_nat_real {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (m : ℕ) (h1 : 0 < m) :
    True :=
  trivial

theorem mun_nat0_real {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (m : ℕ) :
    True :=
  trivial

theorem mun_nat0_int (m : ℕ) :
    True :=
  trivial

theorem mun_pos_int_nat (m : ℤ) (h2 : 0 < m) :
    0 < m :=
  h2

theorem mun_nat0_nonzero (m : ℕ) (h2 : (m : ℤ) ≠ 0) :
    0 < m :=
  LeanBridges.Numbers.nat0_nonzero m h2

theorem mun_integer_step (m : ℤ) (n : ℤ) (h3 : m < n) :
    m + 1 ≤ n :=
  LeanBridges.Numbers.integer_step m n h3

theorem mun_floor_integer {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] [CharZero K] (x : K) :
    True :=
  trivial

theorem mun_floor_below {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] [CharZero K] (x : K) :
    (⌊x⌋ : K) ≤ x :=
  Int.floor_le x

theorem mun_floor_above {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] [CharZero K] (x : K) :
    x < (⌊x⌋ : K) + 1 :=
  Int.lt_floor_add_one x

theorem mun_floor_between {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] [CharZero K] (x : K) (k : ℤ) :
    ⌊x⌋ = k ↔ (k : K) ≤ x ∧ x < (k : K) + 1 :=
  Int.floor_eq_iff

theorem mun_exponent_step {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (m : ℕ) :
    a ^ (m + 1) = a ^ m * a :=
  pow_succ a m

theorem mun_exponent_sum {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (m : ℕ) (n : ℕ) :
    a ^ (m + n) = a ^ m * a ^ n :=
  pow_add a m n

theorem mun_exponent_sum_integer {K : Type*} [Field K] [CharZero K] (a : K) (h2 : a ≠ 0) (m : ℤ) (n : ℤ) :
    a ^ (m + n) = a ^ m * a ^ n :=
  zpow_add₀ h2 m n

theorem mun_exponent_negative {K : Type*} [Field K] [CharZero K] (a : K) (h2 : a ≠ 0) (m : ℤ) :
    a ^ (-m) = 1 / a ^ m :=
  LeanBridges.Numbers.exponent_negative a h2 m

theorem mun_power_cancel {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : K) (m : ℤ) (n : ℤ) (h4 : 1 < a) :
    a ^ m = a ^ n ↔ m = n :=
  zpow_right_inj₀ (by linarith) h4.ne'

theorem mun_product_nonzero {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (x : K) (y : K) (h3 : x ≠ 0) (h4 : y ≠ 0) :
    x * y ≠ 0 :=
  mul_ne_zero h3 h4

theorem mun_power_integer (a : ℤ) (m : ℕ) :
    True :=
  trivial

theorem mun_power_real {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (m : ℕ) :
    True :=
  trivial

theorem mun_nat_minus_one (n : ℕ) (h1 : 0 < n) :
    0 ≤ (n : ℤ) - 1 :=
  LeanBridges.Numbers.nat_minus_one n h1

theorem mun_power_nat (a : ℕ) (h1 : 0 < a) (m : ℕ) :
    0 < (a : ℤ) ^ m :=
  LeanBridges.Numbers.power_nat a h1 m

theorem axi_trichotomy {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    (x < 0 ∨ x = 0) ∨ 0 < x :=
  or_assoc.mpr (lt_trichotomy x 0)

theorem mun_nonneg_or_neg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    0 ≤ x ∨ x < 0 :=
  le_or_gt 0 x

theorem mun_rational_coprime (x : ℚ) :
    ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ (x = (p : ℚ) / (q : ℚ) ∧ (Int.gcd p (q : ℤ) : ℤ) = 1) :=
  ⟨x.num, x.den, x.den_pos, (Rat.num_div_den x).symm, by simp [Int.gcd, x.reduced]⟩

theorem axi_well_ordering (S : Set ℤ) (h1 : S ⊆ {n : ℤ | 0 < n}) (h2 : ∃ s ∈ S, True) :
    ∃ d ∈ S, ∀ s ∈ S, d ≤ s :=
  by obtain ⟨s, hs, -⟩ := h2; classical exact (fun hex : ∃ n : ℕ, (n : ℤ) ∈ S => ⟨Nat.find hex, Nat.find_spec hex, fun t ht => by have h0 : 0 < t := h1 ht; have := Nat.find_min' hex (m := t.toNat) (by rwa [Int.toNat_of_nonneg h0.le]); omega⟩) ⟨s.toNat, by rwa [Int.toNat_of_nonneg (h1 hs).le]⟩

theorem def_abs_1 {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    0 ≤ x → abs x = x :=
  LeanBridges.Numbers.abs_1 x

theorem def_abs_2 {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    x < 0 → abs x = -x :=
  LeanBridges.Numbers.abs_2 x

theorem mun_abs_real {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    True :=
  trivial

theorem mun_abs_difference_lt {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (c : K) (δ : K) :
    abs (x - c) < δ ↔ c - δ < x ∧ x < c + δ :=
  LeanBridges.Numbers.abs_difference_lt x c δ

theorem mun_min_real (x : ℝ) (y : ℝ) :
    True :=
  trivial

theorem mun_min_le_1 (x : ℝ) (y : ℝ) :
    min x y ≤ x :=
  min_le_left x y

theorem mun_min_le_2 (x : ℝ) (y : ℝ) :
    min x y ≤ y :=
  min_le_right x y

theorem mun_lt_min (z : ℝ) (x : ℝ) (y : ℝ) :
    z < min x y ↔ z < x ∧ z < y :=
  lt_min_iff

theorem mun_max_real (x : ℝ) (y : ℝ) :
    True :=
  trivial

theorem mun_le_max_1 (x : ℝ) (y : ℝ) :
    x ≤ max x y :=
  le_max_left x y

theorem mun_le_max_2 (x : ℝ) (y : ℝ) :
    y ≤ max x y :=
  le_max_right x y

theorem mun_quotient_real {K : Type*} [Field K] [CharZero K] (x : K) (y : K) (h3 : y ≠ 0) :
    True :=
  trivial

theorem mun_square_nonneg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    0 ≤ x ^ 2 :=
  sq_nonneg x

theorem mun_square_zero {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (x : K) (h2 : x ^ 2 = 0) :
    x = 0 :=
  LeanBridges.Numbers.square_zero x h2

theorem mun_multiply_le {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (c : K) (h4 : x ≤ y) (h5 : 0 < c) :
    c * x ≤ c * y :=
  mul_le_mul_of_nonneg_left h4 h5.le

theorem mun_square_positive {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (h2 : x ≠ 0) :
    0 < x ^ 2 :=
  lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 h2))

theorem mun_square_equal {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (h3 : 0 ≤ x) (h4 : 0 ≤ y) :
    x ^ 2 = y ^ 2 ↔ x = y :=
  sq_eq_sq₀ h3 h4

theorem mun_square_less {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (h3 : 0 ≤ x) (h4 : 0 ≤ y) :
    x < y ↔ x ^ 2 < y ^ 2 :=
  LeanBridges.Numbers.square_less x y h3 h4

theorem mun_square_le {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (h3 : 0 ≤ x) (h4 : 0 ≤ y) :
    x ≤ y ↔ x ^ 2 ≤ y ^ 2 :=
  LeanBridges.Numbers.square_le x y h3 h4

theorem mun_product_nonneg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (h3 : 0 ≤ x) (h4 : 0 ≤ y) :
    0 ≤ x * y :=
  mul_nonneg h3 h4

theorem mun_product_positive {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (h3 : 0 < x) (h4 : 0 < y) :
    0 < x * y :=
  mul_pos h3 h4

theorem mun_factor_positive {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : K) (b : K) (h3 : 0 ≤ a) (h4 : 0 < a * b) :
    0 < b :=
  pos_of_mul_pos_right h4 h3

theorem mun_power_positive {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : K) (m : ℤ) (h3 : 0 < a) :
    0 < a ^ m :=
  zpow_pos h3 m

theorem mun_zero_product {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (x : K) (y : K) :
    x * y = 0 ↔ x = 0 ∨ y = 0 :=
  mul_eq_zero

theorem mun_quotient_nonneg {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (h3 : 0 ≤ x) (h4 : 0 < y) :
    0 ≤ x / y :=
  div_nonneg h3 h4.le

theorem mun_quotient_positive {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (h3 : 0 < x) (h4 : 0 < y) :
    0 < x / y :=
  div_pos h3 h4

theorem mun_less_scaled {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (c : K) (h4 : 0 < c) :
    x < y ↔ c * x < c * y :=
  LeanBridges.Numbers.less_scaled x y c h4

theorem mun_abs_nonneg (x : ℂ) :
    0 ≤ ‖x‖ :=
  norm_nonneg x

theorem mun_one_power (m : ℤ) :
    (1 ^ m : ℚ) = 1 :=
  one_zpow m

theorem mun_le_cases {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) :
    x ≤ y ↔ x < y ∨ x = y :=
  le_iff_lt_or_eq

theorem mun_divide_le {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (c : K) (h4 : x ≤ y) (h5 : 0 < c) :
    x / c ≤ y / c :=
  LeanBridges.Numbers.divide_le x y c h4 h5

theorem mun_multiply_cancel {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (b : K) (c : K) (h4 : a * c = b * c) (h5 : c ≠ 0) :
    a = b :=
  mul_right_cancel₀ h5 h4

theorem mun_reciprocal_positive {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (h2 : 0 < x) :
    0 < 1 / x :=
  one_div_pos.mpr h2

theorem mun_reciprocal_order {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (h2 : 0 < x) (y : K) (h4 : 0 < y) :
    x ≤ y ↔ 1 / y ≤ 1 / x :=
  (one_div_le_one_div h4 h2).symm

theorem mun_reciprocal_order_strict {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (h2 : 0 < x) (y : K) (h4 : 0 < y) :
    x < y ↔ 1 / y < 1 / x :=
  (one_div_lt_one_div h4 h2).symm

theorem thm_archimedean (x : ℝ) (h2 : 0 < x) :
    ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) < x :=
  LeanBridges.Numbers.archimedean x h2

theorem thm_archimedean_natural (x : ℝ) :
    ∃ m : ℕ, 0 < m ∧ x < (m : ℝ) :=
  LeanBridges.Numbers.archimedean_natural x

theorem mun_abs_product {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) :
    abs (x * y) = abs x * abs y :=
  abs_mul x y

theorem mun_abs_negative {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    abs (-x) = abs x :=
  abs_neg x

theorem mun_abs_integer (z : ℤ) :
    0 ≤ abs z :=
  abs_nonneg z

theorem mun_abs_zero :
    (abs 0 : ℤ) = 0 :=
  abs_zero

theorem mun_abs_square {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    abs x ^ 2 = x ^ 2 :=
  sq_abs x

theorem thm_triangle_inequality {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : K) (b : K) :
    abs (a + b) ≤ abs a + abs b :=
  abs_add_le a b

theorem def_nat0 {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (n : K) :
    (∃ m : ℕ, (m : K) = n) ↔ (∃ m : ℕ, 0 < m ∧ (m : K) = n) ∨ n = 0 :=
  LeanBridges.Numbers.nat0 n

theorem mun_nat0_as_int {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (n : K) :
    (∃ m : ℕ, (m : K) = n) ↔ (∃ m : ℤ, (m : K) = n) ∧ 0 ≤ n :=
  LeanBridges.Numbers.nat0_as_int n

end Parley.Items.Stdlib.Numbers

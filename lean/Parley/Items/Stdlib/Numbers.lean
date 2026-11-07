module

public import Numbers
public import Tactics
public import Batteries.Classes.RatCast
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar

/-! Written from corpus/stdlib/numbers.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Numbers

theorem def_rational {K : Type*} [Field K] [CharZero K] (x : K) :
    (∃ m : ℚ, (m : K) = x) ↔ (∃ p : ℤ, ∃ q : ℤ, 0 < q ∧ x = (p : K) / (q : K)) :=
  LeanBridges.Numbers.rational x

theorem def_i :
    Complex.I * Complex.I = -1 :=
  by (simp_all; done)

theorem mun_i_complex :
    True :=
  by (simp_all; done)

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

theorem mun_nat_closure_1 (a : ℤ) (h1 : 0 < a) (b : ℤ) (h2 : 0 < b) :
    0 < a + b :=
  LeanBridges.Numbers.nat_closure_1 a h1 b h2

theorem mun_nat_closure_2 (a : ℤ) (h1 : 0 < a) (b : ℤ) (h2 : 0 < b) :
    0 < a * b :=
  LeanBridges.Numbers.nat_closure_2 a h1 b h2

theorem mun_real_closure_1 {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (x : K) (y : K) :
    True :=
  trivial

theorem mun_real_closure_2 {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (x : K) (y : K) :
    True :=
  trivial

theorem mun_nat_plus_nat0 (a : ℤ) (h1 : 0 < a) (b : ℤ) (h2 : 0 ≤ b) :
    0 < a + b :=
  by omega

theorem mun_nat0_successor (k : ℤ) (h1 : 0 ≤ k) :
    0 < k + 1 :=
  LeanBridges.Numbers.nat0_successor k h1

theorem mun_nat_int (m : ℤ) (h1 : 0 < m) :
    True :=
  by (simp_all; done)

theorem mun_int_real {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (m : ℤ) :
    True :=
  by simp_all

theorem mun_nat_real {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (m : ℤ) (h1 : 0 < m) :
    True :=
  trivial

theorem mun_nat0_real {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (m : ℤ) (h1 : 0 ≤ m) :
    True :=
  trivial

theorem mun_nat0_int (m : ℤ) (h1 : 0 ≤ m) :
    True :=
  trivial

theorem mun_pos_int_nat (m : ℤ) (h2 : 0 < m) :
    0 < m :=
  h2

theorem mun_nat0_nonzero (m : ℤ) (h1 : 0 ≤ m) (h2 : m ≠ 0) :
    0 < m :=
  LeanBridges.Numbers.nat0_nonzero m h1 h2

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

theorem mun_exponent_step {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (m : ℤ) (h2 : 0 ≤ m) :
    a ^ (m + 1).toNat = a ^ m.toNat * a :=
  by rw [show (m + 1).toNat = m.toNat + 1 by omega, pow_succ]

theorem mun_exponent_sum {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (m : ℤ) (h2 : 0 ≤ m) (n : ℤ) (h3 : 0 ≤ n) :
    a ^ (m + n).toNat = a ^ m.toNat * a ^ n.toNat :=
  by rw [show (m + n).toNat = m.toNat + n.toNat by omega, pow_add]

theorem mun_exponent_sum_integer {K : Type*} [Field K] [CharZero K] (a : K) (h2 : a ≠ 0) (m : ℤ) (n : ℤ) :
    a ^ (m + n) = a ^ m * a ^ n :=
  zpow_add₀ h2 m n

theorem mun_exponent_negative {K : Type*} [Field K] [CharZero K] (a : K) (h2 : a ≠ 0) (m : ℤ) :
    a ^ (-m) = 1 / a ^ m :=
  LeanBridges.Numbers.exponent_negative a h2 m

theorem mun_power_of_power {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (m : ℤ) (h2 : 0 ≤ m) (n : ℤ) (h3 : 0 ≤ n) :
    a ^ (m * n).toNat = (a ^ m.toNat) ^ n.toNat :=
  by rw [Int.toNat_mul h2 h3, pow_mul]

theorem mun_power_of_power_integer {K : Type*} [Field K] [CharZero K] (a : K) (h2 : a ≠ 0) (m : ℤ) (n : ℤ) :
    a ^ (m * n) = (a ^ m) ^ n :=
  zpow_mul a m n

theorem mun_power_of_product {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (b : K) (n : ℤ) (h3 : 0 ≤ n) :
    (a * b) ^ n.toNat = a ^ n.toNat * b ^ n.toNat :=
  mul_pow a b n.toNat

theorem mun_power_of_product_integer {K : Type*} [Field K] [CharZero K] (a : K) (h2 : a ≠ 0) (b : K) (h4 : b ≠ 0) (n : ℤ) :
    (a * b) ^ n = a ^ n * b ^ n :=
  mul_zpow a b n

theorem mun_power_cancel {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : K) (m : ℤ) (n : ℤ) (h4 : 1 < a) :
    a ^ m = a ^ n ↔ m = n :=
  zpow_right_inj₀ (by linarith) h4.ne'

theorem mun_power_order {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : K) (m : ℤ) (n : ℤ) (h4 : 1 < a) :
    m < n ↔ a ^ m < a ^ n :=
  by simp_all

theorem mun_minus_one_even_power (n : ℤ) :
    ((-1) ^ (2 * n) : ℚ) = 1 :=
  by rw [zpow_mul]; simp

theorem mun_minus_one_odd_power (n : ℤ) (h2 : Odd n) :
    ((-1) ^ n : ℚ) = -1 :=
  h2.neg_one_zpow

theorem mun_product_nonzero {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (x : K) (y : K) (h3 : x ≠ 0) (h4 : y ≠ 0) :
    x * y ≠ 0 :=
  mul_ne_zero h3 h4

theorem mun_power_integer (a : ℤ) (m : ℤ) (h2 : 0 ≤ m) :
    True :=
  trivial

theorem mun_power_real {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (m : ℤ) (h2 : 0 ≤ m) :
    True :=
  trivial

theorem mun_power_real_integer {K : Type*} [Field K] [CharZero K] (a : K) (h2 : a ≠ 0) (m : ℤ) :
    True :=
  by (simp_all; done)

theorem mun_power_nat0 (a : ℤ) (h1 : 0 ≤ a) (m : ℤ) (h2 : 0 ≤ m) :
    0 ≤ a ^ m.toNat :=
  by (simp_all; done)

theorem mun_nat_minus_one (n : ℤ) (h1 : 0 < n) :
    0 ≤ n - 1 :=
  LeanBridges.Numbers.nat_minus_one n h1

theorem mun_difference_nat0 (m : ℤ) (h1 : 0 ≤ m) (n : ℤ) (h2 : 0 ≤ n) (h3 : m ≤ n) :
    0 ≤ n - m :=
  by simp_all

theorem mun_integer_sign (n : ℤ) :
    0 ≤ n ∨ 0 ≤ -n :=
  by omega

theorem mun_power_nat (a : ℤ) (h1 : 0 < a) (m : ℤ) (h2 : 0 ≤ m) :
    0 < a ^ m.toNat :=
  LeanBridges.Numbers.power_nat a h1 m h2

theorem mun_real_power_complex (x : ℂ) (y : ℂ) :
    True :=
  by (simp_all; done)

theorem mun_real_power_real (x : ℝ) (h2 : 0 ≤ x) (y : ℝ) :
    True :=
  by (simp_all; done)

theorem mun_real_power_nonneg (x : ℝ) (h2 : 0 ≤ x) (y : ℝ) :
    0 ≤ x ^ y :=
  by positivity

theorem mun_real_power_positive (x : ℝ) (h2 : 0 < x) (y : ℝ) :
    0 < x ^ y :=
  by positivity

theorem mun_real_power_sum (x : ℂ) (h2 : x ≠ 0) (a : ℂ) (b : ℂ) :
    x ^ (a + b) = x ^ a * x ^ b :=
  by exact Complex.cpow_add a b h2

theorem mun_real_power_of_power (x : ℝ) (h2 : 0 < x) (a : ℝ) (b : ℂ) :
    (x : ℂ) ^ ((a : ℂ) * b) = ((x ^ a : ℝ) : ℂ) ^ b :=
  by rw [Complex.ofReal_cpow h2.le, ← Complex.cpow_mul] <;> rw [← Complex.ofReal_log h2.le, ← Complex.ofReal_mul, Complex.ofReal_im] <;> linarith [Real.pi_pos]

theorem mun_root_power (x : ℂ) (n : ℤ) (h2 : 0 < n) :
    (x ^ (1 / (n : ℂ))) ^ n.toNat = x :=
  by lift n to ℕ using h2.le; simp only [Int.toNat_natCast]; push_cast; rw [one_div]; exact Complex.cpow_nat_inv_pow x (by omega)

theorem mun_half_power (x : ℂ) :
    x ^ (1 / 2 : ℂ) = x ^ (1 / 2 : ℂ) :=
  by rfl

theorem axi_trichotomy {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    (x < 0 ∨ x = 0) ∨ 0 < x :=
  or_assoc.mpr (lt_trichotomy x 0)

theorem mun_nonneg_or_neg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    0 ≤ x ∨ x < 0 :=
  le_or_gt 0 x

theorem mun_rational_coprime (x : ℚ) :
    ∃ p : ℤ, ∃ q : ℤ, 0 < q ∧ (x = (p : ℚ) / (q : ℚ) ∧ (Int.gcd p q : ℤ) = 1) :=
  ⟨x.num, x.den, by exact_mod_cast x.den_pos, by push_cast; exact (Rat.num_div_den x).symm, by simp [Int.gcd, x.reduced]⟩

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

theorem mun_abs_difference_le {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (c : K) (δ : K) :
    abs (x - c) ≤ δ ↔ c - δ ≤ x ∧ x ≤ c + δ :=
  by rw [abs_le]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

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

theorem mun_max_le (x : ℝ) (y : ℝ) (z : ℝ) :
    max x y ≤ z ↔ x ≤ z ∧ y ≤ z :=
  by (simp_all; done)

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

theorem mun_multiply_le_nonneg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (c : K) (h4 : x ≤ y) (h5 : 0 ≤ c) :
    x * c ≤ y * c :=
  MulPosMono.mul_le_mul_of_nonneg_right h5 h4

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

theorem mun_power_exponent_le {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : K) (m : ℤ) (h2 : 0 ≤ m) (n : ℤ) (h3 : 0 ≤ n) (h4 : 1 ≤ a) (h5 : m ≤ n) :
    a ^ m.toNat ≤ a ^ n.toNat :=
  by exact pow_le_pow_right₀ h4 (by omega)

theorem mun_power_at_least_one {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : K) (n : ℤ) (h2 : 0 ≤ n) (h3 : 1 ≤ a) :
    1 ≤ a ^ n.toNat :=
  one_le_pow₀ h3

theorem mun_power_nonneg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : K) (m : ℤ) (h2 : 0 ≤ m) (h3 : 0 ≤ a) :
    0 ≤ a ^ m.toNat :=
  by simp_all

theorem mun_zero_power (n : ℤ) (h1 : 0 < n) :
    (0 ^ n.toNat : ℤ) = 0 :=
  by aesop

theorem mun_power_less {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (n : ℤ) (h3 : 0 < n) (h4 : 0 ≤ x) (h5 : x < y) :
    x ^ n.toNat < y ^ n.toNat :=
  pow_lt_pow_left₀ h5 h4 (by omega)

theorem mun_quotients_compared {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (z : K) (w : K) (h5 : 0 ≤ x) (h6 : x ≤ z) (h7 : 0 < w) (h8 : w ≤ y) :
    x / y ≤ z / w :=
  div_le_div₀ (h5.trans h6) h6 h7 h8

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

theorem mun_abs_positive (x : ℂ) :
    x ≠ 0 ↔ 0 < ‖x‖ :=
  by (simp_all; done)

theorem mun_nonzero_integer_abs (z : ℤ) (h2 : z ≠ 0) :
    1 ≤ abs z :=
  Int.one_le_abs h2

theorem mun_abs_nonneg (x : ℂ) :
    0 ≤ ‖x‖ :=
  norm_nonneg x

theorem mun_one_power (m : ℤ) :
    (1 ^ m : ℚ) = 1 :=
  one_zpow m

theorem mun_le_cases {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) :
    x ≤ y ↔ x < y ∨ x = y :=
  le_iff_lt_or_eq

theorem mun_unequal_cases {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) :
    x ≠ y ↔ x < y ∨ y < x :=
  by simp_all

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

theorem mun_cross_multiplied_order {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : K) (b : K) (h3 : 0 < b) (c : K) (d : K) (h6 : 0 < d) :
    a * b < c * d ↔ a / d < c / b :=
  Iff.symm (div_lt_div_iff₀ h6 h3)

theorem thm_bernoulli_inequality {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (n : ℤ) (h2 : 0 ≤ n) (h3 : -1 ≤ x) :
    1 + x * (n : K) ≤ (1 + x) ^ n.toNat :=
  by lift n to ℕ using h2; simp only [Int.toNat_natCast]; have h := one_add_mul_le_pow (by linarith : (-2 : K) ≤ x) n; push_cast; linarith

theorem thm_archimedean (x : ℝ) (h2 : 0 < x) :
    ∃ N : ℤ, 0 < N ∧ 1 / (N : ℝ) < x :=
  LeanBridges.Numbers.archimedean x h2

theorem thm_archimedean_natural (x : ℝ) :
    ∃ m : ℤ, 0 < m ∧ x < (m : ℝ) :=
  LeanBridges.Numbers.archimedean_natural x

theorem mun_abs_product {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) :
    abs (x * y) = abs x * abs y :=
  abs_mul x y

theorem mun_abs_quotient {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (h3 : y ≠ 0) :
    abs (x / y) = abs x / abs y :=
  abs_div x y

theorem mun_abs_negative {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    abs (-x) = abs x :=
  abs_neg x

theorem mun_abs_integer (z : ℤ) :
    0 ≤ abs z :=
  abs_nonneg z

theorem mun_lowest_terms_parts_1 (x : ℚ) :
    True :=
  trivial

theorem mun_lowest_terms_parts_2 (x : ℚ) :
    0 < (Rat.den x : ℤ) :=
  by exact_mod_cast x.den_pos

theorem mun_lowest_terms_parts_3 (x : ℚ) :
    x = (Rat.num x : ℚ) / (Rat.den x : ℚ) :=
  (Rat.num_div_den x).symm

theorem mun_abs_zero :
    (abs 0 : ℤ) = 0 :=
  abs_zero

theorem mun_abs_one :
    (abs 1 : ℤ) = 1 :=
  by simp_all

theorem mun_abs_square {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    abs x ^ 2 = x ^ 2 :=
  sq_abs x

theorem mun_abs_power {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (n : ℤ) (h2 : 0 ≤ n) :
    abs (x ^ n.toNat) = abs x ^ n.toNat :=
  by simp_all

theorem thm_triangle_inequality {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : K) (b : K) :
    abs (a + b) ≤ abs a + abs b :=
  abs_add_le a b

theorem def_nat0 {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (n : K) :
    (∃ m : ℤ, 0 ≤ m ∧ (m : K) = n) ↔ (∃ m : ℤ, 0 < m ∧ (m : K) = n) ∨ n = 0 :=
  LeanBridges.Numbers.nat0 n

theorem mun_nat0_as_int {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (n : K) :
    (∃ m : ℤ, 0 ≤ m ∧ (m : K) = n) ↔ (∃ m : ℤ, (m : K) = n) ∧ 0 ≤ n :=
  LeanBridges.Numbers.nat0_as_int n

end Parley.Items.Stdlib.Numbers

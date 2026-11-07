module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Lean.Parser.Command
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Numbers

Facts of the number systems as the page reads them: the rationals, ℕ₀,
closure and the order of reciprocals, each said in Lean as the build writes
the item.
-/

public section

namespace LeanBridges.Numbers

/-- `def:stdlib/numbers/rational`. -/
theorem rational {K : Type*} [Field K] [CharZero K] (x : K) :
    (∃ m : ℚ, (m : K) = x) ↔ (∃ p : ℤ, ∃ q : ℤ, 0 < q ∧ x = (p : K) / (q : K)) :=
  ⟨fun ⟨m, hm⟩ => ⟨m.num, m.den, by exact_mod_cast m.pos, by rw [← hm, Rat.cast_def]; push_cast; rfl⟩,
   fun ⟨p, q, _, hx⟩ => ⟨(p : ℚ) / q, by rw [hx]; push_cast; rfl⟩⟩

/-- `def:stdlib/numbers/irrational`. -/
theorem irrational (x : ℝ) :
    Irrational x ↔ True ∧ ¬ (∃ m : ℚ, (m : ℝ) = x) :=
  ⟨fun h => ⟨trivial, fun ⟨m, hm⟩ => h ⟨m, hm⟩⟩, fun ⟨_, h⟩ ⟨m, hm⟩ => h ⟨m, hm⟩⟩

/-- `mun:stdlib/numbers/nat-closure`, its sentence 1. -/
theorem nat_closure_1 (a : ℤ) (h1 : 0 < a) (b : ℤ) (h2 : 0 < b) :
    0 < a + b :=
  by omega

/-- `mun:stdlib/numbers/nat-closure`, its sentence 2. -/
theorem nat_closure_2 (a : ℤ) (h1 : 0 < a) (b : ℤ) (h2 : 0 < b) :
    0 < a * b :=
  by positivity

/-- `mun:stdlib/numbers/nat0-successor`. -/
theorem nat0_successor (k : ℤ) (h1 : 0 ≤ k) :
    0 < k + 1 :=
  by omega

/-- `mun:stdlib/numbers/nat0-nonzero`. -/
theorem nat0_nonzero (m : ℤ) (h1 : 0 ≤ m) (h2 : m ≠ 0) :
    0 < m :=
  by omega

/-- `mun:stdlib/numbers/integer-step`. -/
theorem integer_step (m : ℤ) (n : ℤ) (h3 : m < n) :
    m + 1 ≤ n :=
  by omega

/-- `mun:stdlib/numbers/exponent-negative`. -/
theorem exponent_negative {K : Type*} [Field K] [CharZero K] (a : K) (h2 : a ≠ 0) (m : ℤ) :
    a ^ (-m) = 1 / a ^ m :=
  by rw [zpow_neg, one_div]

/-- `mun:stdlib/numbers/nat-minus-one`. -/
theorem nat_minus_one (n : ℤ) (h1 : 0 < n) :
    0 ≤ n - 1 :=
  by omega

/-- `mun:stdlib/numbers/power-nat`. -/
theorem power_nat (a : ℤ) (h1 : 0 < a) (m : ℤ) (h2 : 0 ≤ m) :
    0 < a ^ m.toNat :=
  by positivity

/-- `def:stdlib/numbers/abs`, its sentence 1. -/
theorem abs_1 {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    0 ≤ x → abs x = x :=
  fun h => abs_of_nonneg h

/-- `def:stdlib/numbers/abs`, its sentence 2. -/
theorem abs_2 {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) :
    x < 0 → abs x = -x :=
  fun h => abs_of_neg h

/-- `mun:stdlib/numbers/square-zero`. -/
theorem square_zero {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (x : K) (h2 : x ^ 2 = 0) :
    x = 0 :=
  by simpa using h2

/-- `mun:stdlib/numbers/square-less`. -/
theorem square_less {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (h3 : 0 ≤ x) (h4 : 0 ≤ y) :
    x < y ↔ x ^ 2 < y ^ 2 :=
  ⟨fun h => by nlinarith, fun h => by nlinarith⟩

/-- `mun:stdlib/numbers/square-le`. -/
theorem square_le {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (h3 : 0 ≤ x) (h4 : 0 ≤ y) :
    x ≤ y ↔ x ^ 2 ≤ y ^ 2 :=
  ⟨fun h => by nlinarith, fun h => by nlinarith⟩

/-- `mun:stdlib/numbers/less-scaled`. -/
theorem less_scaled {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (c : K) (h4 : 0 < c) :
    x < y ↔ c * x < c * y :=
  ⟨fun h => by nlinarith, fun h => by nlinarith⟩

/-- `mun:stdlib/numbers/divide-le`. -/
theorem divide_le {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (y : K) (c : K) (h4 : x ≤ y) (h5 : 0 < c) :
    x / c ≤ y / c :=
  by rw [div_le_div_iff_of_pos_right h5]; exact h4

/-- `thm:stdlib/numbers/archimedean-natural`. -/
theorem archimedean_natural (x : ℝ) :
    ∃ m : ℤ, 0 < m ∧ x < (m : ℝ) :=
  by obtain ⟨m, hm⟩ := exists_nat_gt (max x 0); exact ⟨m + 1, by omega, by push_cast; linarith [le_max_left x 0]⟩

/-- `def:stdlib/numbers/nat0`. -/
theorem nat0 {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (n : K) :
    (∃ m : ℤ, 0 ≤ m ∧ (m : K) = n) ↔ (∃ m : ℤ, 0 < m ∧ (m : K) = n) ∨ n = 0 :=
  ⟨fun ⟨m, h0, hm⟩ => h0.eq_or_lt.elim (fun h => Or.inr (by rw [← hm, ← h]; simp)) (fun h => Or.inl ⟨m, h, hm⟩),
   fun h => h.elim (fun ⟨m, hp, hm⟩ => ⟨m, hp.le, hm⟩) (fun h => ⟨0, le_refl _, by rw [h]; simp⟩)⟩

/-- `mun:stdlib/numbers/nat0-as-int`. -/
theorem nat0_as_int {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (n : K) :
    (∃ m : ℤ, 0 ≤ m ∧ (m : K) = n) ↔ (∃ m : ℤ, (m : K) = n) ∧ 0 ≤ n :=
  ⟨fun ⟨m, h0, hm⟩ => ⟨⟨m, hm⟩, by rw [← hm]; exact_mod_cast h0⟩,
   fun ⟨⟨m, hm⟩, h0⟩ => ⟨m, by rw [← hm] at h0; exact_mod_cast h0, hm⟩⟩

/-- `mun:stdlib/numbers/abs-difference-lt`. -/
theorem abs_difference_lt {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (x : K) (c : K) (δ : K) :
    abs (x - c) < δ ↔ c - δ < x ∧ x < c + δ :=
  by rw [abs_sub_lt_iff]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- `thm:stdlib/numbers/archimedean`. -/
theorem archimedean (x : ℝ) (h2 : 0 < x) :
    ∃ N : ℤ, 0 < N ∧ 1 / (N : ℝ) < x :=
  by obtain ⟨N, hN⟩ := exists_nat_one_div_lt h2; exact ⟨N + 1, by omega, by push_cast; exact hN⟩

end LeanBridges.Numbers

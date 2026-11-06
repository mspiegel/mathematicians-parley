module

public import Mathlib

/-!
# Divisibility

Divisibility as the page reads it: primes, the greatest common factor
and remainders, each said in Lean as the build writes the item.
-/

public section

namespace LeanBridges.Divisibility

/-- a mod b of real numbers, as set.mm defines it (`df-mod`): a less the
whole number of b's that fit below it. Mathlib's `%` is of integers; the
`mod` notation writes this one of real numbers. -/
@[expose] noncomputable def mod (a b : ℝ) : ℝ :=
  a - b * ⌊a / b⌋

/-- Of integers, with a divisor not negative, set.mm's mod is Lean's `%`:
a step of integers written with `%` meets an item of real numbers through
it. Below 0 the two differ, `%` keeping a remainder not negative. -/
theorem mod_intCast (a b : ℤ) (hb : 0 ≤ b) :
    mod (a : ℝ) (b : ℝ) = ((a % b : ℤ) : ℝ) := by
  unfold mod
  rcases hb.eq_or_lt with rfl | hb
  · simp
  · have hfloor : ⌊(a : ℝ) / (b : ℝ)⌋ = a / b := by
      rw [Int.floor_eq_iff]
      have hb' : (0 : ℝ) < b := by exact_mod_cast hb
      constructor
      · rw [le_div_iff₀ hb']
        have := Int.ediv_mul_le a hb.ne'
        exact_mod_cast this
      · rw [div_lt_iff₀ hb']
        have := Int.lt_ediv_add_one_mul_self a hb
        push_cast
        exact_mod_cast this
    rw [hfloor, Int.emod_def]
    push_cast
    ring

/-- Of natural numbers, set.mm's mod is Lean's `%` of their integers. -/
theorem mod_natCast (a b : ℕ) :
    mod (a : ℝ) (b : ℝ) = (((a : ℤ) % (b : ℤ) : ℤ) : ℝ) := by
  have := mod_intCast (a : ℤ) (b : ℤ) (by positivity)
  push_cast at this ⊢
  exact this

/-- `thm:stdlib/divisibility/prime-divides-product`. -/
theorem prime_divides_product (p : ℤ) (h1 : 0 < p) (h2 : Nat.Prime p.toNat) (m : ℤ) (n : ℤ) :
    p ∣ m * n ↔ p ∣ m ∨ p ∣ n := by
  lift p to ℕ using h1.le
  simp only [Int.toNat_natCast] at h2
  exact ⟨Int.Prime.dvd_mul' h2, fun h => h.elim (fun h => dvd_mul_of_dvd_left h n) (fun h => dvd_mul_of_dvd_right h m)⟩

/-- `def:stdlib/divisibility/prime`. -/
theorem prime (p : ℤ) (h1 : 0 < p) :
    Nat.Prime p.toNat ↔ 1 < p ∧ (∀ d : ℤ, 0 < d → d ∣ p → d = 1 ∨ d = p) := by
  lift p to ℕ using h1.le
  simp only [Int.toNat_natCast]
  rw [Nat.prime_def]
  constructor
  · rintro ⟨h, hd⟩
    refine ⟨by omega, fun d hd0 hdp => ?_⟩
    lift d to ℕ using hd0.le
    have := hd d (by exact_mod_cast hdp)
    omega
  · rintro ⟨h, hd⟩
    refine ⟨by omega, fun d hdp => ?_⟩
    have := hd d (by exact_mod_cast Nat.pos_of_dvd_of_pos hdp (by omega)) (by exact_mod_cast hdp)
    omega

/-- `def:stdlib/divisibility/gcd`, its sentence 1. -/
theorem gcd_1 (a : ℤ) (h1 : 0 < a) (b : ℤ) (h2 : 0 < b) :
    0 < (Int.gcd a b : ℤ) := by
  have := Int.gcd_pos_of_ne_zero_left b (by omega : a ≠ 0); exact_mod_cast this

/-- `def:stdlib/divisibility/gcd`, its sentence 4. -/
theorem gcd_4 (a : ℤ) (h1 : 0 < a) (b : ℤ) (h2 : 0 < b) :
    ∀ e : ℤ, 0 < e → e ∣ a ∧ e ∣ b → e ≤ (Int.gcd a b : ℤ) :=
  fun e _ h => Int.le_of_dvd (by have := Int.gcd_pos_of_ne_zero_left b (by omega : a ≠ 0); exact_mod_cast this) (Int.dvd_coe_gcd h.1 h.2)

/-- `def:stdlib/divisibility/lcm`, its sentence 1. -/
theorem lcm_1 (a : ℤ) (b : ℤ) :
    0 ≤ (Int.lcm a b : ℤ) :=
  by positivity

/-- `def:stdlib/divisibility/lcm`, its sentence 4. -/
theorem lcm_4 (a : ℤ) (b : ℤ) :
    ∀ k : ℤ, a ∣ k ∧ b ∣ k → (Int.lcm a b : ℤ) ∣ k :=
  fun k h => Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (Int.lcm_dvd (Int.dvd_natAbs.mpr h.1) (Int.dvd_natAbs.mpr h.2)))

/-- `thm:stdlib/divisibility/prime-factor`. -/
theorem prime_factor (m : ℤ) (h1 : 0 < m) (h2 : 1 < m) :
    ∃ p : ℤ, 0 < p ∧ (Nat.Prime p.toNat ∧ p ∣ m) := by
  lift m to ℕ using h1.le
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := m) (by omega)
  exact ⟨p, by exact_mod_cast hp.pos, by simpa using hp, by exact_mod_cast hd⟩

/-- `mun:stdlib/divisibility/divides-one`. -/
theorem divides_one (d : ℤ) (h1 : 0 < d) (h2 : d ∣ (1 : ℤ)) :
    d = 1 :=
  Int.eq_one_of_dvd_one h1.le h2

/-- `mun:stdlib/divisibility/gcd-integer`, its sentence 1. -/
theorem gcd_integer_1 (a : ℤ) (b : ℤ) :
    0 ≤ (Int.gcd a b : ℤ) :=
  by positivity

/-- `mun:stdlib/divisibility/gcd-commutes`. -/
theorem gcd_commutes (a : ℤ) (b : ℤ) :
    (Int.gcd a b : ℤ) = (Int.gcd b a : ℤ) :=
  by rw [Int.gcd_comm]

/-- `mun:stdlib/divisibility/gcd-one`. -/
theorem gcd_one (a : ℤ) :
    (Int.gcd a (1 : ℤ) : ℤ) = 1 :=
  by simp

/-- `mun:stdlib/divisibility/gcd-zero`. -/
theorem gcd_zero (n : ℤ) (h1 : 0 ≤ n) :
    (Int.gcd n (0 : ℤ) : ℤ) = n := by
  simp [abs_of_nonneg h1]

/-- `thm:stdlib/divisibility/gcd-mod`. -/
theorem gcd_mod (a : ℤ) (b : ℤ) (h2 : 0 < b) :
    (Int.gcd (a % b) b : ℤ) = (Int.gcd a b : ℤ) := by
  rw [Int.gcd_emod]

/-- `mun:stdlib/divisibility/mod-remainder`. -/
theorem mod_remainder (a : ℤ) (m : ℤ) (h2 : 0 < m) (r : ℤ) (h3 : 0 ≤ r) (h4 : r < m) :
    a % m = r ↔ (∃ q : ℤ, q * m + r = a) :=
  ⟨fun h => ⟨a / m, by have := Int.ediv_mul_add_emod a m; rw [h] at this; exact this⟩,
   fun ⟨q, hq⟩ => by rw [← hq, add_comm, Int.add_mul_emod_self_right]; exact Int.emod_eq_of_lt h3 h4⟩

/-- `mun:stdlib/divisibility/mod-multiple`. -/
theorem mod_multiple (r : ℤ) (m : ℤ) (h2 : 0 < m) (q : ℤ) :
    (q * m + r) % m = r % m := by
  rw [add_comm, Int.add_mul_emod_self_right]

/-- `mun:stdlib/divisibility/prime-coprime`. -/
theorem prime_coprime (p : ℤ) (h1 : 0 < p) (h2 : Nat.Prime p.toNat) (a : ℤ) (h4 : ¬ p ∣ a) :
    (Int.gcd p a : ℤ) = 1 := by
  lift p to ℕ using h1.le
  simp only [Int.toNat_natCast] at h2
  exact_mod_cast Int.isCoprime_iff_gcd_eq_one.mp ((Nat.prime_iff_prime_int.mp h2).coprime_iff_not_dvd.mpr h4)

/-- `mun:stdlib/divisibility/divides-quotient`. -/
theorem divides_quotient (n : ℤ) (h1 : 0 < n) (d : ℤ) (h2 : 0 < d) :
    d ∣ n ↔ (∃ m : ℤ, 0 < m ∧ (m : ℚ) = (n : ℚ) / (d : ℚ)) := by
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast h2.ne'
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, ?_⟩
    · rcases lt_trichotomy k 0 with h | h | h
      · nlinarith
      · subst h; simp at hk; omega
      · exact h
    · rw [eq_div_iff hd, hk]; push_cast; ring
  · rintro ⟨m, _, hm⟩
    refine ⟨m, ?_⟩
    rw [eq_div_iff hd] at hm
    exact_mod_cast (by linarith : (n : ℚ) = (d : ℚ) * (m : ℚ))

/-- `mun:stdlib/divisibility/prime-nat`. -/
theorem prime_nat (p : ℤ) (h2 : Nat.Prime p.toNat) :
    0 < p :=
  by have := h2.pos; omega

end LeanBridges.Divisibility

module

public import Mathlib

/-!
# Divisibility

Divisibility as the page reads it: primes, the greatest common factor
and remainders, each said in Lean as the build writes the item.
-/

public section

namespace LeanBridges.Divisibility

/-- `thm:stdlib/divisibility/prime-divides-product`. -/
theorem prime_divides_product (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) (m : ℤ) (n : ℤ) :
    (p : ℤ) ∣ m * n ↔ (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n :=
  ⟨Int.Prime.dvd_mul' h2, fun h => h.elim (fun h => dvd_mul_of_dvd_left h n) (fun h => dvd_mul_of_dvd_right h m)⟩

/-- `def:stdlib/divisibility/prime`. -/
theorem prime (p : ℕ) (h1 : 0 < p) :
    Nat.Prime p ↔ 1 < (p : ℤ) ∧ (∀ d : ℕ, 0 < d → (d : ℤ) ∣ (p : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = (p : ℤ)) :=
  by rw [Nat.prime_def]; exact ⟨fun ⟨h, hd⟩ => ⟨by omega, fun d _ hdp => by exact_mod_cast hd d (by exact_mod_cast hdp)⟩, fun ⟨h, hd⟩ => ⟨by omega, fun d hdp => by exact_mod_cast hd d (Nat.pos_of_dvd_of_pos hdp h1) (by exact_mod_cast hdp)⟩⟩

/-- `def:stdlib/divisibility/gcd`, its sentence 1. -/
theorem gcd_1 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    0 < (Int.gcd (a : ℤ) (b : ℤ) : ℤ) :=
  by have := Int.gcd_pos_of_ne_zero_left (b : ℤ) (by omega : (a : ℤ) ≠ 0); exact_mod_cast this

/-- `def:stdlib/divisibility/gcd`, its sentence 4. -/
theorem gcd_4 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    ∀ e : ℕ, 0 < e → (e : ℤ) ∣ (a : ℤ) ∧ (e : ℤ) ∣ (b : ℤ) → (e : ℤ) ≤ (Int.gcd (a : ℤ) (b : ℤ) : ℤ) :=
  fun e he h => Int.le_of_dvd (by have := Int.gcd_pos_of_ne_zero_left (b : ℤ) (by omega : (a : ℤ) ≠ 0); exact_mod_cast this) (Int.dvd_coe_gcd h.1 h.2)

/-- `def:stdlib/divisibility/lcm`, its sentence 1. -/
theorem lcm_1 (a : ℤ) (b : ℤ) :
    0 ≤ (Int.lcm a b : ℤ) :=
  by positivity

/-- `def:stdlib/divisibility/lcm`, its sentence 4. -/
theorem lcm_4 (a : ℤ) (b : ℤ) :
    ∀ k : ℤ, a ∣ k ∧ b ∣ k → (Int.lcm a b : ℤ) ∣ k :=
  fun k h => Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (Int.lcm_dvd (Int.dvd_natAbs.mpr h.1) (Int.dvd_natAbs.mpr h.2)))

/-- `thm:stdlib/divisibility/prime-factor`. -/
theorem prime_factor (m : ℕ) (h1 : 0 < m) (h2 : 1 < (m : ℤ)) :
    ∃ p : ℕ, 0 < p ∧ (Nat.Prime p ∧ (p : ℤ) ∣ (m : ℤ)) :=
  by obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := m) (by omega); exact ⟨p, hp.pos, hp, by exact_mod_cast hd⟩

/-- `mun:stdlib/divisibility/divides-one`. -/
theorem divides_one (d : ℕ) (h1 : 0 < d) (h2 : (d : ℤ) ∣ (1 : ℤ)) :
    (d : ℤ) = 1 :=
  by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h2

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
theorem gcd_zero (n : ℕ) :
    (Int.gcd (n : ℤ) (0 : ℤ) : ℤ) = (n : ℤ) :=
  by simp

/-- `thm:stdlib/divisibility/gcd-mod`. -/
theorem gcd_mod (a : ℤ) (b : ℕ) (h2 : 0 < b) :
    (Int.gcd (a % (b : ℤ)) (b : ℤ) : ℤ) = (Int.gcd a (b : ℤ) : ℤ) :=
  by rw [Int.gcd_emod]

/-- `mun:stdlib/divisibility/mod-remainder`. -/
theorem mod_remainder (a : ℤ) (m : ℕ) (h2 : 0 < m) (r : ℕ) (h4 : (r : ℤ) < (m : ℤ)) :
    a % (m : ℤ) = (r : ℤ) ↔ (∃ q : ℤ, q * (m : ℤ) + (r : ℤ) = a) :=
  ⟨fun h => ⟨a / (m : ℤ), by have := Int.ediv_mul_add_emod a m; rw [h] at this; exact this⟩, fun ⟨q, hq⟩ => by rw [← hq, add_comm, Int.add_mul_emod_self_right]; exact Int.emod_eq_of_lt (by omega) (by omega)⟩

/-- `mun:stdlib/divisibility/mod-multiple`. -/
theorem mod_multiple (r : ℤ) (m : ℕ) (h2 : 0 < m) (q : ℤ) :
    (q * (m : ℤ) + r) % (m : ℤ) = r % (m : ℤ) :=
  by rw [add_comm, Int.add_mul_emod_self_right]

/-- `mun:stdlib/divisibility/prime-coprime`. -/
theorem prime_coprime (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) (a : ℤ) (h4 : ¬ (p : ℤ) ∣ a) :
    (Int.gcd (p : ℤ) a : ℤ) = 1 :=
  by exact_mod_cast Int.isCoprime_iff_gcd_eq_one.mp ((Nat.prime_iff_prime_int.mp h2).coprime_iff_not_dvd.mpr h4)

/-- `mun:stdlib/divisibility/divides-quotient`. -/
theorem divides_quotient (n : ℕ) (h1 : 0 < n) (d : ℕ) (h2 : 0 < d) :
    (d : ℤ) ∣ (n : ℤ) ↔ (∃ m : ℕ, 0 < m ∧ (m : ℚ) = (n : ℚ) / (d : ℚ)) :=
  ⟨fun ⟨k, hk⟩ => ⟨k.toNat, by have hk0 : 0 < k := (by rcases lt_trichotomy k 0 with h | h | h <;> [nlinarith; (subst h; simp at hk; omega); exact h]); omega, by have hk0 : (0:ℤ) ≤ k := (by rcases lt_trichotomy k 0 with h | h | h <;> [nlinarith; omega; omega]); rw [show ((k.toNat : ℕ) : ℚ) = ((k : ℤ) : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk0]; field_simp; rw [mul_comm]; exact_mod_cast hk.symm⟩, fun ⟨m, _, hm⟩ => ⟨m, by field_simp at hm; exact_mod_cast (by linarith : (n : ℚ) = (d : ℚ) * (m : ℚ))⟩⟩

end LeanBridges.Divisibility

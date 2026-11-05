module

public import Divisibility
public import Tactics

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

theorem mun_odd_not_even (n : ℤ) (h2 : Odd n) :
    ¬ Even n :=
  Int.not_even_iff_odd.mpr h2

theorem mun_odd_not_divisible (n : ℤ) (h2 : Odd n) :
    ¬ (2 : ℤ) ∣ n :=
  by rw [Int.two_dvd_ne_zero]; exact Int.odd_iff.1 h2

theorem mun_odd_plus_odd (a : ℤ) (h2 : Odd a) (b : ℤ) (h4 : Odd b) :
    Even (a + b) :=
  Odd.add_odd h2 h4

theorem mun_odd_minus_odd (a : ℤ) (h2 : Odd a) (b : ℤ) (h4 : Odd b) :
    Even (a - b) :=
  Odd.sub_odd h2 h4

theorem mun_odd_plus_even (a : ℤ) (h2 : Odd a) (b : ℤ) (h4 : Even b) :
    Odd (a + b) :=
  Odd.add_even h2 h4

theorem mun_odd_minus_even (a : ℤ) (h2 : Odd a) (b : ℤ) (h4 : Even b) :
    Odd (a - b) :=
  Odd.sub_even h2 h4

theorem mun_even_product (a : ℤ) (h2 : Even a) (x : ℤ) :
    Even (a * x) :=
  h2.mul_right x

theorem mun_even_product_factor (a : ℤ) (b : ℤ) :
    Even (a * b) ↔ Even a ∨ Even b :=
  Int.even_mul

theorem thm_prime_divides_product (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) (m : ℤ) (n : ℤ) :
    (p : ℤ) ∣ m * n ↔ (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n :=
  LeanBridges.Divisibility.prime_divides_product p h1 h2 m n

theorem thm_prime_divides_power (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) (a : ℤ) (n : ℕ) (h4 : 0 < n) :
    (p : ℤ) ∣ a ^ n ↔ (p : ℤ) ∣ a :=
  by exact ⟨fun h => Int.Prime.dvd_pow' h2 h, fun h => dvd_pow h (Nat.pos_iff_ne_zero.mp h4)⟩

theorem thm_divides_gcd (d : ℤ) (a : ℤ) (b : ℤ) (h4 : d ∣ a) (h5 : d ∣ b) :
    d ∣ (Int.gcd a b : ℤ) :=
  Int.dvd_coe_gcd h4 h5

theorem thm_division_algorithm (n : ℕ) (h1 : 0 < n) (d : ℕ) (h2 : 0 < d) :
    ∃ q : ℤ, ∃ r : ℤ, ((n : ℤ) = q * (d : ℤ) + r ∧ 0 ≤ r) ∧ r < (d : ℤ) :=
  ⟨(n : ℤ) / d, (n : ℤ) % d, ⟨by rw [mul_comm]; exact (Int.mul_ediv_add_emod _ _).symm, Int.emod_nonneg _ (by omega)⟩, Int.emod_lt_of_pos _ (by omega)⟩

theorem def_prime (p : ℕ) (h1 : 0 < p) :
    Nat.Prime p ↔ 1 < (p : ℤ) ∧ (∀ d : ℕ, 0 < d → (d : ℤ) ∣ (p : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = (p : ℤ)) :=
  LeanBridges.Divisibility.prime p h1

theorem def_gcd_1 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    0 < (Int.gcd (a : ℤ) (b : ℤ) : ℤ) :=
  LeanBridges.Divisibility.gcd_1 a h1 b h2

theorem def_gcd_2 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    (Int.gcd (a : ℤ) (b : ℤ) : ℤ) ∣ (a : ℤ) :=
  Int.gcd_dvd_left a b

theorem def_gcd_3 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    (Int.gcd (a : ℤ) (b : ℤ) : ℤ) ∣ (b : ℤ) :=
  Int.gcd_dvd_right a b

theorem def_gcd_4 (a : ℕ) (h1 : 0 < a) (b : ℕ) (h2 : 0 < b) :
    ∀ e : ℕ, 0 < e → (e : ℤ) ∣ (a : ℤ) ∧ (e : ℤ) ∣ (b : ℤ) → (e : ℤ) ≤ (Int.gcd (a : ℤ) (b : ℤ) : ℤ) :=
  LeanBridges.Divisibility.gcd_4 a h1 b h2

theorem def_lcm_1 (a : ℤ) (b : ℤ) :
    0 ≤ (Int.lcm a b : ℤ) :=
  LeanBridges.Divisibility.lcm_1 a b

theorem def_lcm_2 (a : ℤ) (b : ℤ) :
    a ∣ (Int.lcm a b : ℤ) :=
  Int.dvd_lcm_left a b

theorem def_lcm_3 (a : ℤ) (b : ℤ) :
    b ∣ (Int.lcm a b : ℤ) :=
  Int.dvd_lcm_right a b

theorem def_lcm_4 (a : ℤ) (b : ℤ) :
    ∀ k : ℤ, a ∣ k ∧ b ∣ k → (Int.lcm a b : ℤ) ∣ k :=
  LeanBridges.Divisibility.lcm_4 a b

theorem mun_lcm_times_gcd (a : ℤ) (b : ℤ) :
    (Int.lcm a b : ℤ) * (Int.gcd a b : ℤ) = abs (a * b) :=
  by rw [abs_mul, Int.abs_eq_natAbs, Int.abs_eq_natAbs, mul_comm]; exact_mod_cast Int.gcd_mul_lcm a b

theorem thm_prime_factor (m : ℕ) (h1 : 0 < m) (h2 : 1 < (m : ℤ)) :
    ∃ p : ℕ, 0 < p ∧ (Nat.Prime p ∧ (p : ℤ) ∣ (m : ℤ)) :=
  LeanBridges.Divisibility.prime_factor m h1 h2

theorem mun_divides_sum (d : ℤ) (a : ℤ) (b : ℤ) (h4 : d ∣ a) (h5 : d ∣ b) :
    d ∣ a + b :=
  dvd_add h4 h5

theorem mun_divides_difference (d : ℤ) (a : ℤ) (b : ℤ) (h4 : d ∣ a) (h5 : d ∣ b) :
    d ∣ a - b :=
  dvd_sub h4 h5

theorem mun_divides_one (d : ℕ) (h1 : 0 < d) (h2 : (d : ℤ) ∣ (1 : ℤ)) :
    (d : ℤ) = 1 :=
  LeanBridges.Divisibility.divides_one d h1 h2

theorem mun_divides_combination (e : ℤ) (a : ℤ) (b : ℤ) (x : ℤ) (y : ℤ) (h6 : e ∣ a) (h7 : e ∣ b) :
    e ∣ a * x + b * y :=
  dvd_add (Dvd.dvd.mul_right h6 x) (Dvd.dvd.mul_right h7 y)

theorem mun_divides_le (e : ℕ) (h1 : 0 < e) (m : ℕ) (h2 : 0 < m) (h3 : (e : ℤ) ∣ (m : ℤ)) :
    (e : ℤ) ≤ (m : ℤ) :=
  Int.le_of_dvd (by omega) h3

theorem mun_below_not_divisible (n : ℕ) (h1 : 0 < n) (x : ℕ) (h2 : 0 < x) (h3 : (x : ℤ) < (n : ℤ)) :
    ¬ (n : ℤ) ∣ (x : ℤ) :=
  by intro h; have := Int.le_of_dvd (by omega) h; omega

theorem def_congruent_mod (n : ℤ) (a : ℤ) (b : ℤ) :
    a ≡ b [ZMOD n] ↔ n ∣ a - b :=
  Int.modEq_comm.trans Int.modEq_iff_dvd

theorem mun_divides_multiple (e : ℤ) (a : ℤ) (x : ℤ) (h4 : e ∣ a) :
    e ∣ a * x :=
  Dvd.dvd.mul_right h4 x

theorem mun_congruent_divides (m : ℤ) (a : ℤ) (b : ℤ) (h4 : a ≡ b [ZMOD m]) :
    m ∣ a ↔ m ∣ b :=
  Int.ModEq.dvd_iff h4

theorem mun_gcd_integer_1 (a : ℤ) (b : ℤ) :
    0 ≤ (Int.gcd a b : ℤ) :=
  LeanBridges.Divisibility.gcd_integer_1 a b

theorem mun_gcd_integer_2 (a : ℤ) (b : ℤ) :
    (Int.gcd a b : ℤ) ∣ a :=
  Int.gcd_dvd_left a b

theorem mun_gcd_integer_3 (a : ℤ) (b : ℤ) :
    (Int.gcd a b : ℤ) ∣ b :=
  Int.gcd_dvd_right a b

theorem mun_gcd_natural (a : ℤ) (b : ℤ) (h3 : ¬ (a = 0 ∧ b = 0)) :
    0 < (Int.gcd a b : ℤ) :=
  by have h0 : Int.gcd a b ≠ 0 := (by intro h0; rw [Int.gcd_eq_zero_iff] at h0; exact h3 h0); omega

theorem mun_gcd_scaled (c : ℕ) (a : ℤ) (b : ℤ) :
    (Int.gcd ((c : ℤ) * a) ((c : ℤ) * b) : ℤ) = (c : ℤ) * (Int.gcd a b : ℤ) :=
  by rw [Int.gcd_mul_left]; simp

theorem mun_gcd_scaled_integer (c : ℤ) (a : ℤ) (b : ℤ) :
    (Int.gcd (c * a) (c * b) : ℤ) = abs (c * (Int.gcd a b : ℤ)) :=
  by rw [Int.gcd_mul_left, abs_mul]; simp

theorem mun_gcd_negative (a : ℤ) (b : ℤ) :
    (Int.gcd (-a) b : ℤ) = (Int.gcd a b : ℤ) :=
  by (simp_all; done)

theorem mun_gcd_commutes (a : ℤ) (b : ℤ) :
    (Int.gcd a b : ℤ) = (Int.gcd b a : ℤ) :=
  LeanBridges.Divisibility.gcd_commutes a b

theorem mun_gcd_one (a : ℤ) :
    (Int.gcd a (1 : ℤ) : ℤ) = 1 :=
  LeanBridges.Divisibility.gcd_one a

theorem mun_gcd_zero (n : ℕ) :
    (Int.gcd (n : ℤ) (0 : ℤ) : ℤ) = (n : ℤ) :=
  LeanBridges.Divisibility.gcd_zero n

theorem thm_gcd_mod (a : ℤ) (b : ℕ) (h2 : 0 < b) :
    (Int.gcd (a % (b : ℤ)) (b : ℤ) : ℤ) = (Int.gcd a (b : ℤ) : ℤ) :=
  LeanBridges.Divisibility.gcd_mod a b h2

theorem mun_mod_natural (a : ℤ) (b : ℕ) (h2 : 0 < b) :
    0 ≤ a % (b : ℤ) :=
  Int.emod_nonneg a (by omega)

theorem mun_mod_less (a : ℤ) (b : ℕ) (h2 : 0 < b) :
    a % (b : ℤ) < (b : ℤ) :=
  Int.emod_lt_of_pos a (by omega)

theorem mun_mod_remainder (a : ℤ) (m : ℕ) (h2 : 0 < m) (r : ℕ) (h4 : (r : ℤ) < (m : ℤ)) :
    a % (m : ℤ) = (r : ℤ) ↔ (∃ q : ℤ, q * (m : ℤ) + (r : ℤ) = a) :=
  LeanBridges.Divisibility.mod_remainder a m h2 r h4

theorem mun_mod_multiple (r : ℤ) (m : ℕ) (h2 : 0 < m) (q : ℤ) :
    (q * (m : ℤ) + r) % (m : ℤ) = r % (m : ℤ) :=
  LeanBridges.Divisibility.mod_multiple r m h2 q

theorem mun_mod_real (a : ℝ) (b : ℝ) (h3 : 0 < b) :
    True :=
  by (simp_all; done)

theorem mun_mod_value (a : ℝ) (b : ℝ) (h3 : 0 < b) :
    LeanBridges.Divisibility.mod a b = a - b * (⌊a / b⌋ : ℝ) :=
  rfl

theorem mun_mod_below (a : ℝ) (b : ℝ) (h3 : 0 ≤ a) (h4 : a < b) :
    LeanBridges.Divisibility.mod a b = a :=
  by unfold LeanBridges.Divisibility.mod; have hb : 0 < b := (by linarith); have h0 : ⌊a / b⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨div_nonneg h3 hb.le, (div_lt_one hb).2 h4⟩; rw [h0]; simp

theorem mun_zero_divides (n : ℤ) :
    (0 : ℤ) ∣ n ↔ n = 0 :=
  zero_dvd_iff

theorem mun_divides_self (n : ℤ) :
    n ∣ n :=
  dvd_refl n

theorem mun_prime_nat (p : ℤ) (h2 : Nat.Prime p.toNat) :
    0 < p :=
  LeanBridges.Divisibility.prime_nat p h2

theorem mun_two_prime :
    Nat.Prime (2 : ℤ).toNat :=
  by norm_num at *

theorem mun_prime_coprime (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) (a : ℤ) (h4 : ¬ (p : ℤ) ∣ a) :
    (Int.gcd (p : ℤ) a : ℤ) = 1 :=
  LeanBridges.Divisibility.prime_coprime p h1 h2 a h4

theorem def_perfect (n : ℕ) (h1 : 0 < n) :
    ArithmeticFunction.sigma 1 n = 2 * n ↔ (ArithmeticFunction.sigma 1 n : ℤ) = 2 * (n : ℤ) :=
  by omega

theorem thm_sigma_multiplicative (m : ℕ) (h1 : 0 < m) (n : ℕ) (h2 : 0 < n) (h3 : (Int.gcd (m : ℤ) (n : ℤ) : ℤ) = 1) :
    (ArithmeticFunction.sigma 1 (m * n) : ℤ) = (ArithmeticFunction.sigma 1 m : ℤ) * (ArithmeticFunction.sigma 1 n : ℤ) :=
  by have hc : Nat.Coprime m n := (by have h := h3; rw [Int.gcd_natCast_natCast] at h; exact_mod_cast h); exact_mod_cast ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc

theorem thm_sigma_prime (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) :
    (ArithmeticFunction.sigma 1 p : ℤ) = (p : ℤ) + 1 :=
  by have h := ArithmeticFunction.sigma_one_apply_prime_pow h2 (i := 1); rw [pow_one] at h; rw [h]; push_cast [Finset.sum_range_succ]; ring

theorem thm_sigma_prime_power (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) (k : ℕ) :
    (ArithmeticFunction.sigma 1 (p ^ k) : ℚ) = (∑ j ∈ Finset.Icc (0 : ℤ) (k : ℤ), ((p : ℚ) ^ j : ℚ)) :=
  by rw [ArithmeticFunction.sigma_one_apply_prime_pow h2]; push_cast; rw [(show Finset.Icc (0 : ℤ) (k : ℤ) = (Finset.range (k + 1)).map ⟨fun i : ℕ => (i : ℤ), Nat.cast_injective⟩ by ext j; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]; constructor; (rintro ⟨h0, hk⟩; exact ⟨j.toNat, by omega, by omega⟩); (rintro ⟨i, hi, rfl⟩; omega))]; simp [zpow_natCast]

theorem mun_sigma_nat (n : ℕ) (h1 : 0 < n) :
    0 < (ArithmeticFunction.sigma 1 n : ℤ) :=
  by (simp_all; done)

theorem mun_sigma_part (Y : Set ℤ) (n : ℕ) (h1 : 0 < n) (h2 : Y ⊆ {d : ℤ | 0 < d ∧ d ∣ (n : ℤ)}) :
    (∑ᶠ d ∈ Y, (d : ℤ)) ≤ (ArithmeticFunction.sigma 1 n : ℤ) :=
  by have hD : Y ⊆ ((n.divisors.map ⟨fun i : ℕ => (i : ℤ), Nat.cast_injective⟩ : Finset ℤ) : Set ℤ) := (by intro d hd; obtain ⟨hp, hdv⟩ := h2 hd; simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe, Nat.mem_divisors]; refine ⟨d.natAbs, ⟨?_, (by omega)⟩, (by omega)⟩; have := Int.natAbs_dvd_natAbs.mpr hdv; simpa using this); have hfin : Y.Finite := (Finset.finite_toSet _).subset hD; rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ArithmeticFunction.sigma_one_apply]; push_cast; have hmap : ∑ x ∈ n.divisors, (x : ℤ) = ∑ x ∈ n.divisors.map ⟨fun i : ℕ => (i : ℤ), Nat.cast_injective⟩, x := (by simp [Finset.sum_map]); rw [hmap]; apply Finset.sum_le_sum_of_subset_of_nonneg; (intro d hd; have := hD ((Set.Finite.mem_toFinset hfin).mp hd); simpa using this); (intro d hd _; simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hd; obtain ⟨i, _, rfl⟩ := hd; positivity)

theorem mun_one_divides (n : ℤ) :
    (1 : ℤ) ∣ n :=
  by simp_all

theorem mun_coprime_power (a : ℤ) (b : ℤ) (k : ℕ) (h4 : (Int.gcd a b : ℤ) = 1) :
    (Int.gcd (a ^ k) b : ℤ) = 1 :=
  by have h : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.2 (by exact_mod_cast h4); exact_mod_cast Int.isCoprime_iff_gcd_eq_one.1 (h.pow_left (m := k))

theorem def_phi (n : ℕ) (h1 : 0 < n) :
    (Nat.totient n : ℤ) = ({r ∈ (Set.Icc (0 : ℤ) ((n : ℤ) - 1) : Set ℤ) | (Int.gcd r (n : ℤ) : ℤ) = 1}.ncard : ℤ) :=
  by rw [Nat.totient_eq_card_coprime]; have e : {r ∈ (Set.Icc (0 : ℤ) ((n : ℤ) - 1) : Set ℤ) | (Int.gcd r (n : ℤ) : ℤ) = 1} = (((Finset.range n).filter n.Coprime).map ⟨fun i : ℕ => (i : ℤ), Nat.cast_injective⟩ : Finset ℤ) := (by ext r; simp only [Set.mem_setOf_eq, Set.mem_Icc, Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]; constructor; (rintro ⟨⟨h0, hr⟩, hg⟩; refine ⟨r.toNat, ⟨(by omega), ?_⟩, (by omega)⟩; rw [Nat.coprime_comm, Nat.Coprime, ← Int.gcd_natCast_natCast, Int.toNat_of_nonneg h0]; exact_mod_cast hg); (rintro ⟨i, ⟨hi, hc⟩, rfl⟩; refine ⟨⟨(by omega), (by omega)⟩, ?_⟩; rw [Int.gcd_natCast_natCast, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.mp hc)]; rfl)); rw [e, Set.ncard_coe_finset, Finset.card_map]

theorem mun_phi_natural (n : ℕ) (h1 : 0 < n) :
    0 < (Nat.totient n : ℤ) :=
  by (simp_all; done)

theorem thm_phi_prime (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) :
    (Nat.totient p : ℤ) = (p : ℤ) - 1 :=
  by rw [Nat.totient_prime h2]; push_cast [Nat.cast_sub h2.one_le]; ring

theorem mun_coprime_product (x : ℤ) (y : ℤ) (n : ℕ) (h3 : 0 < n) (h4 : (Int.gcd x (n : ℤ) : ℤ) = 1) (h5 : (Int.gcd y (n : ℤ) : ℤ) = 1) :
    (Int.gcd (x * y) (n : ℤ) : ℤ) = 1 :=
  by have h4' : IsCoprime x (n : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 (by exact_mod_cast h4); have h5' : IsCoprime y (n : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 (by exact_mod_cast h5); exact_mod_cast Int.isCoprime_iff_gcd_eq_one.1 (h4'.mul_left h5')

theorem mun_congruent_in_range (n : ℕ) (h1 : 0 < n) (x : ℤ) (h2 : x ∈ Finset.Icc (0 : ℤ) ((n : ℤ) - 1)) (y : ℤ) (h3 : y ∈ Finset.Icc (0 : ℤ) ((n : ℤ) - 1)) (h4 : x ≡ y [ZMOD (n : ℤ)]) :
    x = y :=
  by simp only [Finset.mem_Icc] at h2 h3; have h := Int.ModEq.eq h4; rw [Int.emod_eq_of_lt h2.1 (by omega), Int.emod_eq_of_lt h3.1 (by omega)] at h; exact h

theorem mun_mod_congruent (x : ℤ) (n : ℕ) (h2 : 0 < n) :
    x ≡ (x % (n : ℤ)) [ZMOD (n : ℤ)] :=
  Int.ModEq.symm (Int.mod_modEq x ↑n)

theorem mun_minus_one_congruent (n : ℕ) (h1 : 0 < n) :
    ((n : ℤ) - 1) ≡ (-1 : ℤ) [ZMOD (n : ℤ)] :=
  Int.modEq_add_modulus_iff.mp rfl

theorem mun_mod_equal_congruent (x : ℤ) (y : ℤ) (n : ℕ) (h3 : 0 < n) (h4 : x % (n : ℤ) = y % (n : ℤ)) :
    x ≡ y [ZMOD (n : ℤ)] :=
  h4

theorem mun_divides_square (d : ℤ) (n : ℤ) :
    d ∣ n ↔ d ^ 2 ∣ n ^ 2 :=
  by simp_all

theorem mun_divides_quotient (n : ℕ) (h1 : 0 < n) (d : ℕ) (h2 : 0 < d) :
    (d : ℤ) ∣ (n : ℤ) ↔ (∃ m : ℕ, 0 < m ∧ (m : ℚ) = (n : ℚ) / (d : ℚ)) :=
  LeanBridges.Divisibility.divides_quotient n h1 d h2

theorem mun_divides_transitive (d : ℤ) (e : ℤ) (n : ℤ) (h4 : d ∣ e) (h5 : e ∣ n) :
    d ∣ n :=
  Int.dvd_trans h4 h5

theorem thm_bezout (a : ℤ) (b : ℕ) (h2 : 0 < b) :
    ∃ x : ℤ, ∃ y : ℤ, a * x + (b : ℤ) * y = (Int.gcd a (b : ℤ) : ℤ) :=
  ⟨Int.gcdA a b, Int.gcdB a b, (Int.gcd_eq_gcd_ab a b).symm⟩

theorem thm_coprime_divides (x : ℤ) (c : ℤ) (n : ℕ) (h3 : 0 < n) (h4 : (n : ℤ) ∣ x * c) (h5 : (Int.gcd c (n : ℤ) : ℤ) = 1) :
    (n : ℤ) ∣ x :=
  Int.dvd_of_dvd_mul_left_of_gcd_one h4 (by rw [Int.gcd_comm]; exact_mod_cast h5)

theorem thm_congruent_cancel (x : ℤ) (y : ℤ) (c : ℤ) (n : ℕ) (h4 : 0 < n) (h5 : (x * c) ≡ (y * c) [ZMOD (n : ℤ)]) (h6 : (Int.gcd c (n : ℤ) : ℤ) = 1) :
    x ≡ y [ZMOD (n : ℤ)] :=
  by have h := Int.ModEq.cancel_right_div_gcd (by exact_mod_cast h4 : (0 : ℤ) < n) h5; have hg : Int.gcd (n : ℤ) c = 1 := (by rw [Int.gcd_comm]; exact_mod_cast h6); rw [hg] at h; simpa using h

theorem mun_prime_power_not_less (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) (a : ℕ) (a' : ℕ) (m : ℤ) (m' : ℤ) (h7 : (Int.gcd m (p : ℤ) : ℤ) = 1) (h8 : (p : ℤ) ^ a * m = (p : ℤ) ^ a' * m') :
    ¬ (a : ℤ) < (a' : ℤ) :=
  by intro hlt; have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 h2; have hle : a + 1 ≤ a' := (by omega); have hdvd : (p : ℤ) ^ (a + 1) ∣ (p : ℤ) ^ a * m := (h8 ▸ Dvd.dvd.mul_right (pow_dvd_pow _ hle) _); rw [pow_succ] at hdvd; have hpm : (p : ℤ) ∣ m := (mul_dvd_mul_iff_left (pow_ne_zero a hp.ne_zero)).1 hdvd; have hc : IsCoprime m (p : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 (by exact_mod_cast h7); exact hp.not_unit (hc.isUnit_of_dvd' hpm (dvd_refl _))

theorem mun_prime_power_unique (p : ℕ) (h1 : 0 < p) (h2 : Nat.Prime p) (a : ℕ) (a' : ℕ) (m : ℤ) (m' : ℤ) (h7 : (Int.gcd m (p : ℤ) : ℤ) = 1) (h8 : (Int.gcd m' (p : ℤ) : ℤ) = 1) (h9 : (p : ℤ) ^ a * m = (p : ℤ) ^ a' * m') :
    (a : ℤ) = (a' : ℤ) :=
  by by_contra hne; have hne' : a ≠ a' := (by intro e; exact hne (by rw [e])); rcases Nat.lt_or_gt_of_ne hne' with h | h; exacts [mun_prime_power_not_less p h1 h2 a a' m m' h7 h9 (by exact_mod_cast h), mun_prime_power_not_less p h1 h2 a' a m' m h8 h9.symm (by exact_mod_cast h)]

theorem thm_prime_powers_unique_1 (a : ℕ) (b : ℕ) (c : ℕ) (a' : ℕ) (b' : ℕ) (c' : ℕ) (h7 : (2 ^ a * 3 ^ b * 5 ^ c : ℤ) = 2 ^ a' * 3 ^ b' * 5 ^ c') :
    (a : ℤ) = (a' : ℤ) :=
  by have h : 2 ^ a * 3 ^ b * 5 ^ c = 2 ^ a' * 3 ^ b' * 5 ^ c' := (by exact_mod_cast h7); have key : ∀ x y z : ℕ, (2 ^ x * 3 ^ y * 5 ^ z).factorization 2 = x ∧ (2 ^ x * 3 ^ y * 5 ^ z).factorization 3 = y ∧ (2 ^ x * 3 ^ y * 5 ^ z).factorization 5 = z := (by intro x y z; rw [Nat.factorization_mul (by positivity) (by positivity), Nat.factorization_mul (by positivity) (by positivity)]; simp [Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_three.factorization, Nat.prime_five.factorization, Finsupp.single_apply]); have := (key a b c).1; rw [h, (key a' b' c').1] at this; exact_mod_cast this.symm

theorem thm_prime_powers_unique_2 (a : ℕ) (b : ℕ) (c : ℕ) (a' : ℕ) (b' : ℕ) (c' : ℕ) (h7 : (2 ^ a * 3 ^ b * 5 ^ c : ℤ) = 2 ^ a' * 3 ^ b' * 5 ^ c') :
    (b : ℤ) = (b' : ℤ) :=
  by have h : 2 ^ a * 3 ^ b * 5 ^ c = 2 ^ a' * 3 ^ b' * 5 ^ c' := (by exact_mod_cast h7); have key : ∀ x y z : ℕ, (2 ^ x * 3 ^ y * 5 ^ z).factorization 2 = x ∧ (2 ^ x * 3 ^ y * 5 ^ z).factorization 3 = y ∧ (2 ^ x * 3 ^ y * 5 ^ z).factorization 5 = z := (by intro x y z; rw [Nat.factorization_mul (by positivity) (by positivity), Nat.factorization_mul (by positivity) (by positivity)]; simp [Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_three.factorization, Nat.prime_five.factorization, Finsupp.single_apply]); have := (key a b c).2.1; rw [h, (key a' b' c').2.1] at this; exact_mod_cast this.symm

theorem thm_prime_powers_unique_3 (a : ℕ) (b : ℕ) (c : ℕ) (a' : ℕ) (b' : ℕ) (c' : ℕ) (h7 : (2 ^ a * 3 ^ b * 5 ^ c : ℤ) = 2 ^ a' * 3 ^ b' * 5 ^ c') :
    (c : ℤ) = (c' : ℤ) :=
  by have h : 2 ^ a * 3 ^ b * 5 ^ c = 2 ^ a' * 3 ^ b' * 5 ^ c' := (by exact_mod_cast h7); have key : ∀ x y z : ℕ, (2 ^ x * 3 ^ y * 5 ^ z).factorization 2 = x ∧ (2 ^ x * 3 ^ y * 5 ^ z).factorization 3 = y ∧ (2 ^ x * 3 ^ y * 5 ^ z).factorization 5 = z := (by intro x y z; rw [Nat.factorization_mul (by positivity) (by positivity), Nat.factorization_mul (by positivity) (by positivity)]; simp [Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_three.factorization, Nat.prime_five.factorization, Finsupp.single_apply]); have := (key a b c).2.2; rw [h, (key a' b' c').2.2] at this; exact_mod_cast this.symm

theorem thm_product_coprime (X : Set ℤ) (h1 : X ⊆ (Set.univ : Set ℤ)) (h2 : X.Finite) (n : ℕ) (h3 : 0 < n) (h4 : ∀ y ∈ X, (Int.gcd y (n : ℤ) : ℤ) = 1) :
    (Int.gcd (∏ᶠ x ∈ X, (x : ℤ)) (n : ℤ) : ℤ) = 1 :=
  by rw [finprod_mem_eq_finite_toFinset_prod _ h2]; have h := IsCoprime.prod_left (t := h2.toFinset) (s := fun i : ℤ => i) (fun i hi => Int.isCoprime_iff_gcd_eq_one.2 (by exact_mod_cast h4 i (h2.mem_toFinset.1 hi)) : ∀ i ∈ h2.toFinset, IsCoprime i (n : ℤ)); exact_mod_cast Int.isCoprime_iff_gcd_eq_one.1 h

theorem thm_product_congruent_termwise {α : Type*} (t : α → ℤ) (u : α → ℤ) (X : Set α) (h1 : X.Finite) (n : ℕ) (h2 : 0 < n) (h3 : ∀ x ∈ X, (t x) ≡ (u x) [ZMOD (n : ℤ)]) :
    (∏ᶠ x ∈ X, (t x : ℤ)) ≡ (∏ᶠ x ∈ X, (u x : ℤ)) [ZMOD (n : ℤ)] :=
  by rw [finprod_mem_eq_finite_toFinset_prod _ h1, finprod_mem_eq_finite_toFinset_prod _ h1]; exact Int.ModEq.prod fun x hx => h3 x ((Set.Finite.mem_toFinset h1).mp hx)

theorem thm_product_congruent (f : ℤ → ℤ) (X : Set ℤ) (h1 : X ⊆ (Set.univ : Set ℤ)) (h2 : X.Finite) (c : ℤ) (n : ℕ) (h4 : 0 < n) (h5 : ∀ y ∈ X, (y * c) ≡ (f y) [ZMOD (n : ℤ)]) (hf : Set.MapsTo f X X) :
    (∏ᶠ x ∈ X, (x * c : ℤ)) ≡ (∏ᶠ x ∈ X, (f x : ℤ)) [ZMOD (n : ℤ)] :=
  by rw [finprod_mem_eq_finite_toFinset_prod _ h2, finprod_mem_eq_finite_toFinset_prod _ h2, ← ZMod.intCast_eq_intCast_iff]; push_cast; exact Finset.prod_congr rfl (fun y hy => (by have h := (ZMod.intCast_eq_intCast_iff _ _ _).2 (h5 y (h2.mem_toFinset.1 hy)); push_cast at h; exact h))

end Parley.Items.Stdlib.Divisibility

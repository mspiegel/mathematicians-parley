module

public import LeanBridges

/-! Written from corpus/stdlib/counting.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Counting

theorem def_factorial_1 :
    (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) = 1 :=
  by simp

theorem def_factorial_2 :
    (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 :=
  by simp

theorem def_factorial_3 (n : ℕ) :
    (LeanBridges.Counting.factorial ((n : ℤ) + 1) : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) * ((n : ℤ) + 1) :=
  by rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, LeanBridges.Counting.factorial_natCast, LeanBridges.Counting.factorial_natCast, Nat.factorial_succ]; push_cast; ring

theorem mun_factorial_nat (n : ℕ) :
    0 < (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  by simpa using Nat.factorial_pos n

theorem mun_factorial_at_most (m : ℕ) (n : ℕ) (h3 : (m : ℤ) ≤ (n : ℤ)) :
    (LeanBridges.Counting.factorial (m : ℤ) : ℤ) ≤ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  by simpa using Nat.factorial_le (show m ≤ n by exact_mod_cast h3)

theorem mun_factorial_divisible (n : ℕ) (h1 : 0 < n) (m : ℕ) (h2 : 0 < m) (h3 : (m : ℤ) ≤ (n : ℤ)) :
    (m : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  by simpa using Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial h2 (show m ≤ n by exact_mod_cast h3))

theorem def_C_1 (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (-1 : ℤ) : ℤ) = 0 :=
  by simp [LeanBridges.Counting.choose]

theorem def_C_2 (n : ℕ) (k : ℤ) :
    k ∈ Finset.Icc (0 : ℤ) (n : ℤ) → (LeanBridges.Counting.choose (n : ℤ) k : ℚ) = (LeanBridges.Counting.factorial (n : ℤ) : ℚ) / ((LeanBridges.Counting.factorial ((n : ℤ) - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) :=
  by intro h; obtain ⟨h0, h1⟩ := Finset.mem_Icc.mp h; lift k to ℕ using h0; have hk : k ≤ n := (by exact_mod_cast h1); rw [show (n : ℤ) - (k : ℤ) = ((n - k : ℕ) : ℤ) from (Nat.cast_sub hk).symm]; simp only [LeanBridges.Counting.choose_natCast, LeanBridges.Counting.factorial_natCast]; rw [Nat.cast_choose ℚ hk, mul_comm]

theorem def_C_3 (n : ℕ) (k : ℤ) :
    (n : ℤ) < k → (LeanBridges.Counting.choose (n : ℤ) k : ℤ) = 0 :=
  by intro h; have h0 : (0 : ℤ) ≤ k := (by omega); lift k to ℕ using h0; have hk : n < k := (by exact_mod_cast h); simp [Nat.choose_eq_zero_of_lt hk]

theorem thm_pascal (n : ℕ) (k : ℤ) :
    (LeanBridges.Counting.choose (n : ℤ) k : ℤ) + (LeanBridges.Counting.choose (n : ℤ) (k - 1) : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + 1) k : ℤ) :=
  LeanBridges.Counting.pascal n k

theorem thm_absorption (n : ℕ) (k : ℤ) (h2 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    (LeanBridges.Counting.choose ((n : ℤ) + 1) (k + 1) : ℚ) = (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) :=
  LeanBridges.Counting.absorption n k h2

theorem mun_binomial_zero_index (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (0 : ℤ) : ℤ) = 1 :=
  by simp [LeanBridges.Counting.choose]

theorem mun_binomial_one (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (1 : ℤ) : ℤ) = (n : ℤ) :=
  by simp [LeanBridges.Counting.choose]

theorem mun_binomial_all (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (n : ℤ) : ℤ) = 1 :=
  by simp

theorem mun_binomial_two (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 :=
  by simp [LeanBridges.Counting.choose, Nat.cast_choose_two]

theorem mun_binomial_outside (n : ℕ) (k : ℤ) (h3 : ¬ k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    (LeanBridges.Counting.choose (n : ℤ) k : ℤ) = 0 :=
  LeanBridges.Counting.choose_outside n k h3

theorem mun_binomial_nat0 (n : ℕ) (k : ℤ) :
    0 ≤ (LeanBridges.Counting.choose (n : ℤ) k : ℤ) :=
  by positivity

theorem mun_binomial_nat (n : ℕ) (k : ℤ) (h2 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    0 < (LeanBridges.Counting.choose (n : ℤ) k : ℤ) :=
  LeanBridges.Counting.choose_pos n k h2

theorem mun_factorial_nonzero (n : ℕ) :
    (LeanBridges.Counting.factorial (n : ℤ) : ℤ) ≠ 0 :=
  by simp [Nat.factorial_ne_zero]

end Parley.Items.Stdlib.Counting

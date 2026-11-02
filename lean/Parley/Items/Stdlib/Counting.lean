module

public import LeanBridges

/-! Written from corpus/stdlib/counting.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Counting

theorem def_factorial_1 :
    (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) = 1 :=
  LeanBridges.Counting.factorial_1

theorem def_factorial_2 :
    (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 :=
  LeanBridges.Counting.factorial_2

theorem def_factorial_3 (n : ℕ) :
    (LeanBridges.Counting.factorial ((n : ℤ) + 1) : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) * ((n : ℤ) + 1) :=
  LeanBridges.Counting.factorial_3 n

theorem mun_factorial_nat (n : ℕ) :
    0 < (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  LeanBridges.Counting.factorial_nat n

theorem mun_factorial_at_most (m : ℕ) (n : ℕ) (h3 : (m : ℤ) ≤ (n : ℤ)) :
    (LeanBridges.Counting.factorial (m : ℤ) : ℤ) ≤ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  LeanBridges.Counting.factorial_at_most m n h3

theorem mun_factorial_divisible (n : ℕ) (h1 : 0 < n) (m : ℕ) (h2 : 0 < m) (h3 : (m : ℤ) ≤ (n : ℤ)) :
    (m : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  LeanBridges.Counting.factorial_divisible n h1 m h2 h3

theorem def_C_1 (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (-1 : ℤ) : ℤ) = 0 :=
  LeanBridges.Counting.C_1 n

theorem def_C_2 (n : ℕ) (k : ℤ) :
    k ∈ Finset.Icc (0 : ℤ) (n : ℤ) → (LeanBridges.Counting.choose (n : ℤ) k : ℚ) = (LeanBridges.Counting.factorial (n : ℤ) : ℚ) / ((LeanBridges.Counting.factorial ((n : ℤ) - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) :=
  LeanBridges.Counting.C_2 n k

theorem def_C_3 (n : ℕ) (k : ℤ) :
    (n : ℤ) < k → (LeanBridges.Counting.choose (n : ℤ) k : ℤ) = 0 :=
  LeanBridges.Counting.C_3 n k

theorem thm_pascal (n : ℕ) (k : ℤ) :
    (LeanBridges.Counting.choose (n : ℤ) k : ℤ) + (LeanBridges.Counting.choose (n : ℤ) (k - 1) : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + 1) k : ℤ) :=
  LeanBridges.Counting.pascal n k

theorem thm_absorption (n : ℕ) (k : ℤ) (h2 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    (LeanBridges.Counting.choose ((n : ℤ) + 1) (k + 1) : ℚ) = (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) :=
  LeanBridges.Counting.absorption n k h2

theorem mun_binomial_zero_index (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (0 : ℤ) : ℤ) = 1 :=
  LeanBridges.Counting.binomial_zero_index n

theorem mun_binomial_one (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (1 : ℤ) : ℤ) = (n : ℤ) :=
  LeanBridges.Counting.binomial_one n

theorem mun_binomial_all (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (n : ℤ) : ℤ) = 1 :=
  LeanBridges.Counting.binomial_all n

theorem mun_binomial_two (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 :=
  LeanBridges.Counting.binomial_two n

theorem mun_binomial_outside (n : ℕ) (k : ℤ) (h3 : ¬ k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    (LeanBridges.Counting.choose (n : ℤ) k : ℤ) = 0 :=
  LeanBridges.Counting.choose_outside n k h3

theorem mun_binomial_nat0 (n : ℕ) (k : ℤ) :
    0 ≤ (LeanBridges.Counting.choose (n : ℤ) k : ℤ) :=
  LeanBridges.Counting.binomial_nat0 n k

theorem mun_binomial_nat (n : ℕ) (k : ℤ) (h2 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    0 < (LeanBridges.Counting.choose (n : ℤ) k : ℤ) :=
  LeanBridges.Counting.choose_pos n k h2

theorem mun_factorial_nonzero (n : ℕ) :
    (LeanBridges.Counting.factorial (n : ℤ) : ℤ) ≠ 0 :=
  LeanBridges.Counting.factorial_nonzero n

end Parley.Items.Stdlib.Counting

module

public import Sums
public import Tactics

/-! Written from corpus/stdlib/sums.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Sums

theorem mun_sum_integer (t : ℤ → ℤ) (n : ℕ) :
    True :=
  by simp_all

theorem mun_sum_difference (t : ℤ → ℤ) (u : ℤ → ℤ) (n : ℕ) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (t k - u k : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (t k : ℤ)) - (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (u k : ℤ)) :=
  by simp_all

theorem mun_sum_single {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) :
    (∑ k ∈ Finset.Icc a a, (t k : K)) = t a :=
  LeanBridges.Sums.sum_single t a

theorem mun_sum_last {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (n : ℕ) :
    (∑ k ∈ Finset.Icc (0 : ℤ) ((n : ℤ) + 1), (t k : K)) = (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (t k : K)) + t ((n : ℤ) + 1) :=
  LeanBridges.Sums.sum_last t n

theorem mun_sum_extended {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (a : ℤ) (n : ℤ) (h3 : a ≤ n) :
    (∑ k ∈ Finset.Icc a (n + 1), (t k : K)) = (∑ k ∈ Finset.Icc a n, (t k : K)) + t (n + 1) :=
  LeanBridges.Sums.sum_extended t a n h3

theorem mun_sum_first {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (n : ℕ) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (t k : K)) = t 0 + (∑ k ∈ Finset.Icc (0 + 1 : ℤ) (n : ℤ), (t k : K)) :=
  LeanBridges.Sums.sum_first t n

theorem mun_sum_shift {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (c : ℤ) :
    (∑ k ∈ Finset.Icc a b, (t k : K)) = (∑ k ∈ Finset.Icc (a + c) (b + c), (t (k - c) : K)) :=
  LeanBridges.Sums.sum_shift t a b c

theorem mun_sum_scaled {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (c : K) :
    c * (∑ k ∈ Finset.Icc a b, (t k : K)) = (∑ k ∈ Finset.Icc a b, (c * t k : K)) :=
  Finset.mul_sum _ _ _

theorem mun_sum_add {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (u : ℤ → K) (a : ℤ) (b : ℤ) :
    (∑ k ∈ Finset.Icc a b, (t k + u k : K)) = (∑ k ∈ Finset.Icc a b, (t k : K)) + (∑ k ∈ Finset.Icc a b, (u k : K)) :=
  Finset.sum_add_distrib

theorem mun_sum_termwise {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (u : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → t k = u k) :
    (∑ k ∈ Finset.Icc a b, (t k : K)) = (∑ k ∈ Finset.Icc a b, (u k : K)) :=
  Finset.sum_congr rfl h3

theorem mun_sum_termwise_complex {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (u : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → t k = u k) :
    (∑ k ∈ Finset.Icc a b, (t k : K)) = (∑ k ∈ Finset.Icc a b, (u k : K)) :=
  Finset.sum_congr rfl h3

theorem mun_sum_real {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) :
    True :=
  trivial

theorem mun_product_real {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) :
    True :=
  trivial

theorem mun_product_range_nonneg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → 0 ≤ t k) :
    0 ≤ (∏ k ∈ Finset.Icc a b, (t k : K)) :=
  Finset.prod_nonneg h3

theorem mun_product_single {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) :
    (∏ k ∈ Finset.Icc a a, (t k : K)) = t a :=
  LeanBridges.Sums.product_single t a

theorem mun_product_extended {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (a : ℤ) (n : ℤ) (h3 : a ≤ n) :
    (∏ k ∈ Finset.Icc a (n + 1), (t k : K)) = (∏ k ∈ Finset.Icc a n, (t k : K)) * t (n + 1) :=
  LeanBridges.Sums.product_extended t a n h3

theorem mun_range_difference (a : ℤ) (n : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a n) :
    0 ≤ n - k :=
  LeanBridges.Sums.range_difference a n k h3

theorem mun_range_integer (a : ℤ) (b : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a b) :
    True :=
  by simp_all

theorem mun_range_nat0 (n : ℤ) (k : ℤ) (h2 : k ∈ Finset.Icc (0 : ℤ) n) :
    0 ≤ k :=
  (Finset.mem_Icc.mp h2).1

theorem def_range (k : ℤ) (n : ℤ) :
    k ∈ Finset.Icc (1 : ℤ) n ↔ 0 < k ∧ k ≤ n :=
  by rw [Finset.mem_Icc]; omega

theorem def_range0 (k : ℤ) (n : ℕ) :
    k ∈ Finset.Icc (0 : ℤ) (n : ℤ) ↔ 0 ≤ k ∧ k ≤ (n : ℤ) :=
  Finset.mem_Icc

theorem mun_range_without_last (n : ℕ) (h1 : 0 < n) :
    (Set.Icc (1 : ℤ) (n : ℤ) : Set ℤ) = (Set.Icc (1 : ℤ) ((n : ℤ) + 1) : Set ℤ) \ ({(n : ℤ) + 1} : Set ℤ) :=
  by aesop

theorem mun_range_end (n : ℕ) (h1 : 0 < n) :
    (n : ℤ) ∈ Finset.Icc (1 : ℤ) (n : ℤ) :=
  by aesop

theorem mun_range_within (a : ℤ) (k : ℤ) (n : ℤ) (h4 : k ≤ n) :
    (Set.Icc a k : Set ℤ) ⊆ (Set.Icc a n : Set ℤ) :=
  Set.Icc_subset_Icc_right h4

theorem mun_range_inside (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ) (h5 : c ≤ a) (h6 : b ≤ d) :
    (Set.Icc a b : Set ℤ) ⊆ (Set.Icc c d : Set ℤ) :=
  Set.Icc_subset_Icc h5 h6

theorem def_range_between (k : ℤ) (a : ℤ) (b : ℤ) :
    k ∈ Finset.Icc a b ↔ a ≤ k ∧ k ≤ b :=
  Finset.mem_Icc

theorem mun_range_bounds_1 (a : ℤ) (b : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a b) :
    a ≤ k :=
  (Finset.mem_Icc.mp h3).1

theorem mun_range_bounds_2 (a : ℤ) (b : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a b) :
    k ≤ b :=
  (Finset.mem_Icc.mp h3).2

theorem mun_sum_split {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (c : ℤ) (h4 : a ≤ b + 1) (h5 : b ≤ c) :
    (∑ k ∈ Finset.Icc a c, (t k : K)) = (∑ k ∈ Finset.Icc a b, (t k : K)) + (∑ k ∈ Finset.Icc (b + 1) c, (t k : K)) :=
  LeanBridges.Sums.sum_split t a b c h4 h5

theorem mun_sum_le {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (u : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → t k ≤ u k) :
    (∑ k ∈ Finset.Icc a b, (t k : K)) ≤ (∑ k ∈ Finset.Icc a b, (u k : K)) :=
  Finset.sum_le_sum h3

theorem mun_sum_constant {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (a : ℤ) (b : ℤ) (h3 : a ≤ b) (c : K) :
    (∑ k ∈ Finset.Icc a b, (c : K)) = ((b : K) - (a : K) + 1) * c :=
  LeanBridges.Sums.sum_constant a b h3 c

theorem mun_sum_nonneg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → 0 ≤ t k) :
    0 ≤ (∑ k ∈ Finset.Icc a b, (t k : K)) :=
  Finset.sum_nonneg h3

theorem mun_range_finite (a : ℤ) (b : ℤ) :
    (Set.Icc a b : Set ℤ).Finite :=
  by simp_all

theorem mun_range_in_integers (a : ℤ) (b : ℤ) :
    (Set.Icc a b : Set ℤ) ⊆ (Set.univ : Set ℤ) :=
  by simp_all

theorem mun_range_from_bounds (m : ℕ) (h1 : 0 < m) (x : ℕ) (h3 : (x : ℤ) < (m : ℤ)) :
    (x : ℤ) ∈ Finset.Icc (0 : ℤ) ((m : ℤ) - 1) :=
  LeanBridges.Sums.range_from_bounds m h1 x h3

end Parley.Items.Stdlib.Sums

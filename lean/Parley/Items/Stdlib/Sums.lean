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

theorem thm_sum_telescopes {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : a ≤ b + 1) :
    (∑ k ∈ Finset.Icc a b, (t k - t (k + 1) : K)) = t a - t (b + 1) :=
  by obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a - 1 + n := ⟨(b - (a - 1)).toNat, by omega⟩; subst hn; clear h3; induction n with | zero => (simp only [Nat.cast_zero, add_zero]; rw [Finset.Icc_eq_empty_of_lt (by omega)]; simp) | succ k ih => (rw [(show a - 1 + ((k + 1 : ℕ) : ℤ) = (a - 1 + k) + 1 by push_cast; ring), (show Finset.Icc a (a - 1 + k + 1) = insert (a - 1 + k + 1) (Finset.Icc a (a - 1 + k)) by ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega), Finset.sum_insert (by simp), ih]; ring)

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

theorem mun_product_first {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : a ≤ b) :
    (∏ k ∈ Finset.Icc a b, (t k : K)) = t a * (∏ k ∈ Finset.Icc (a + 1) b, (t k : K)) :=
  by rw [(show Finset.Icc a b = insert a (Finset.Icc (a + 1) b) by ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega), Finset.prod_insert (by simp)]

theorem mun_product_termwise (t : ℂ → ℂ) (u : ℂ → ℂ) (X : Set ℂ) (Z : Set ℂ) (Y : Set ℂ) (W : Set ℂ) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → t (k : ℂ) = u (k : ℂ)) (ht : Set.MapsTo t X Z) (hu : Set.MapsTo u Y W) :
    (∏ k ∈ Finset.Icc a b, (t (k : ℂ) : ℂ)) = (∏ k ∈ Finset.Icc a b, (u (k : ℂ) : ℂ)) :=
  Finset.prod_congr rfl h3

theorem mun_range_difference (a : ℤ) (n : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a n) :
    0 ≤ n - k :=
  LeanBridges.Sums.range_difference a n k h3

theorem mun_range_integer (a : ℤ) (b : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a b) :
    True :=
  by simp_all

theorem mun_range_nat0 (n : ℤ) (k : ℤ) (h2 : k ∈ Finset.Icc (0 : ℤ) n) :
    0 ≤ k :=
  (Finset.mem_Icc.mp h2).1

theorem mun_range_nat (n : ℤ) (k : ℤ) (h2 : k ∈ Finset.Icc (1 : ℤ) n) :
    0 < k :=
  by (aesop)

theorem def_range (k : ℤ) (n : ℤ) :
    k ∈ Finset.Icc (1 : ℤ) n ↔ 0 < k ∧ k ≤ n :=
  by rw [Finset.mem_Icc]; omega

theorem def_range0 (k : ℤ) (n : ℕ) :
    k ∈ Finset.Icc (0 : ℤ) (n : ℤ) ↔ 0 ≤ k ∧ k ≤ (n : ℤ) :=
  Finset.mem_Icc

theorem mun_range_single (m : ℤ) :
    (Set.Icc m m : Set ℤ) = ({m} : Set ℤ) :=
  by (simp_all; done)

theorem mun_range_empty :
    (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) = ∅ :=
  by (simp_all; done)

theorem mun_range_split (m : ℤ) (n : ℤ) (k : ℤ) (h1 : k ∈ Finset.Icc m n) :
    (Set.Icc m n : Set ℤ) = (Set.Icc m k : Set ℤ) ∪ (Set.Icc (k + 1) n : Set ℤ) :=
  by simp only [Finset.mem_Icc] at h1; ext x; simp only [Set.mem_union, Set.mem_Icc]; omega

theorem mun_range_extended (a : ℤ) (b : ℤ) (k : ℤ) (h1 : k ∈ Finset.Icc a b) :
    k ∈ Finset.Icc a (b + 1) :=
  by simp only [Finset.mem_Icc] at h1 ⊢; omega

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

theorem mun_sum_constant_over {α : Type*} (X : Set α) (h1 : X.Finite) (c : ℂ) :
    (∑ᶠ x ∈ X, (c : ℂ)) = (X.ncard : ℂ) * c :=
  by rw [finsum_mem_eq_finite_toFinset_sum _ h1, Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ h1]

theorem mun_sum_empty_range {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : b < a) :
    (∑ k ∈ Finset.Icc a b, (t k : K)) = 0 :=
  by (simp_all; done)

theorem mun_sum_of_three (a : ℝ) (b : ℝ) (c : ℝ) (h4 : a ≠ b) (h5 : a ≠ c) (h6 : b ≠ c) :
    (∑ᶠ d ∈ ({a, b, c} : Set ℝ), (d : ℝ)) = a + b + c :=
  by rw [finsum_mem_insert _ (by simp [h4, h5]) (Set.toFinite _), finsum_mem_pair h6]; ring

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

theorem mun_product_integer (X : Set ℤ) (h1 : X ⊆ (Set.univ : Set ℤ)) (h2 : X.Finite) :
    True :=
  by (simp_all; done)

theorem mun_product_of_ones {α : Type*} (X : Set α) (h1 : X.Finite) :
    (∏ᶠ x ∈ X, (1 : ℤ)) = 1 :=
  by (simp_all; done)

theorem mun_product_constant {α : Type*} (X : Set α) (h1 : X.Finite) (c : ℝ) :
    (∏ᶠ x ∈ X, (c : ℝ)) = c ^ X.ncard :=
  by rw [finprod_mem_eq_finite_toFinset_prod _ h1, Finset.prod_const, Set.ncard_eq_toFinset_card _ h1]

theorem thm_product_factor (X : Set ℤ) (h1 : X ⊆ (Set.univ : Set ℤ)) (h2 : X.Finite) (c : ℤ) :
    (∏ᶠ x ∈ X, (x * c : ℤ)) = c ^ X.ncard * (∏ᶠ x ∈ X, (x : ℤ)) :=
  by rw [finprod_mem_eq_finite_toFinset_prod _ h2, finprod_mem_eq_finite_toFinset_prod _ h2, Finset.prod_mul_distrib, Finset.prod_const, Set.ncard_eq_toFinset_card _ h2]; ring

end Parley.Items.Stdlib.Sums

module

public import LeanBridges

/-! Written from corpus/stdlib/sums.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Sums

theorem mun_sum_single {K : Type*} [CommRing K] [IsDomain K] (t : ℤ → K) (a : ℤ) :
    (∑ k ∈ Finset.Icc a a, t k) = t a :=
  by simp

theorem mun_sum_extended {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] (t : ℤ → K) (a : ℤ) (n : ℤ) (h3 : a ≤ n) :
    (∑ k ∈ Finset.Icc a (n + 1), t k) = (∑ k ∈ Finset.Icc a n, t k) + t (n + 1) :=
  LeanBridges.Sums.sum_extended t a n h3

theorem mun_sum_termwise {K : Type*} [CommRing K] [IsDomain K] (t : ℤ → K) (u : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → t k = u k) :
    (∑ k ∈ Finset.Icc a b, t k) = (∑ k ∈ Finset.Icc a b, u k) :=
  Finset.sum_congr rfl h3

theorem mun_sum_termwise_complex {K : Type*} [CommRing K] [IsDomain K] (t : ℤ → K) (u : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → t k = u k) :
    (∑ k ∈ Finset.Icc a b, t k) = (∑ k ∈ Finset.Icc a b, u k) :=
  Finset.sum_congr rfl h3

theorem mun_range_difference (a : ℤ) (n : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a n) :
    0 ≤ n - k :=
  by have := Finset.mem_Icc.mp h3; omega

theorem def_range_between (k : ℤ) (a : ℤ) (b : ℤ) :
    k ∈ Finset.Icc a b ↔ a ≤ k ∧ k ≤ b :=
  Finset.mem_Icc

theorem mun_range_bounds_1 (a : ℤ) (b : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a b) :
    a ≤ k :=
  (Finset.mem_Icc.mp h3).1

theorem mun_range_bounds_2 (a : ℤ) (b : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a b) :
    k ≤ b :=
  (Finset.mem_Icc.mp h3).2

end Parley.Items.Stdlib.Sums

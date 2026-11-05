module

public import Mathlib

/-!
# Sums over a range of integers

The page's Σ(k = a to b) t(k) is `∑ k ∈ Finset.Icc a b, t k` with a, b and
k integers, as the index of a sum always is in the Lean build. Mathlib
states the step that adds a range's last term for ranges of naturals; this
is the same step for integers.
-/

public section

namespace LeanBridges.Sums

/-- A sum to n + 1 is the sum to n and the last term, where a ≤ n:
`mun:stdlib/sums/sum-extended`. -/
theorem sum_extended {M : Type*} [AddCommMonoid M] (t : ℤ → M) (a n : ℤ) (h : a ≤ n) :
    (∑ k ∈ Finset.Icc a (n + 1), t k) = (∑ k ∈ Finset.Icc a n, t k) + t (n + 1) := by
  have split : Finset.Icc a (n + 1) = insert (n + 1) (Finset.Icc a n) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [split, Finset.sum_insert (by simp), add_comm]

end LeanBridges.Sums

namespace LeanBridges.Sums

/-- `mun:stdlib/sums/sum-single`. -/
theorem sum_single {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) :
    (∑ k ∈ Finset.Icc a a, (t k : K)) = t a :=
  by simp

/-- `mun:stdlib/sums/sum-last`. -/
theorem sum_last {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (n : ℕ) :
    (∑ k ∈ Finset.Icc (0 : ℤ) ((n : ℤ) + 1), (t k : K)) = (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (t k : K)) + t ((n : ℤ) + 1) :=
  by rw [show Finset.Icc (0 : ℤ) ((n : ℤ) + 1) = insert ((n : ℤ) + 1) (Finset.Icc 0 (n : ℤ)) by ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega, Finset.sum_insert (by simp), add_comm]

/-- `mun:stdlib/sums/sum-first`. -/
theorem sum_first {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (n : ℕ) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (t k : K)) = t 0 + (∑ k ∈ Finset.Icc (0 + 1 : ℤ) (n : ℤ), (t k : K)) :=
  by rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.sum_cons]; congr 1; apply Finset.sum_congr _ (fun _ _ => rfl); ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega

/-- `mun:stdlib/sums/sum-shift`. -/
theorem sum_shift {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (c : ℤ) :
    (∑ k ∈ Finset.Icc a b, (t k : K)) = (∑ k ∈ Finset.Icc (a + c) (b + c), (t (k - c) : K)) :=
  by rw [← Finset.map_add_right_Icc, Finset.sum_map]; simp

/-- `mun:stdlib/sums/product-single`. -/
theorem product_single {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) :
    (∏ k ∈ Finset.Icc a a, (t k : K)) = t a :=
  by simp

/-- `mun:stdlib/sums/product-extended`. -/
theorem product_extended {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (n : ℤ) (h3 : a ≤ n) :
    (∏ k ∈ Finset.Icc a (n + 1), (t k : K)) = (∏ k ∈ Finset.Icc a n, (t k : K)) * t (n + 1) :=
  by rw [show Finset.Icc a (n + 1) = insert (n + 1) (Finset.Icc a n) by ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega, Finset.prod_insert (by simp), mul_comm]

/-- `mun:stdlib/sums/range-difference`. -/
theorem range_difference (a : ℤ) (n : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a n) :
    0 ≤ n - k :=
  by have := Finset.mem_Icc.mp h3; omega

/-- `mun:stdlib/sums/sum-split`. -/
theorem sum_split {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (c : ℤ) (h4 : a ≤ b + 1) (h5 : b ≤ c) :
    (∑ k ∈ Finset.Icc a c, (t k : K)) = (∑ k ∈ Finset.Icc a b, (t k : K)) + (∑ k ∈ Finset.Icc (b + 1) c, (t k : K)) :=
  by rw [← Finset.sum_union (Finset.disjoint_left.mpr fun x hx hx' => by simp only [Finset.mem_Icc] at hx hx'; omega)]; congr 1; ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega

/-- `mun:stdlib/sums/sum-constant`. -/
theorem sum_constant {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : ℤ) (b : ℤ) (h3 : a ≤ b) (c : K) :
    (∑ k ∈ Finset.Icc a b, (c : K)) = ((b : K) - (a : K) + 1) * c :=
  by rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]; congr 1; have h : ((b + 1 - a).toNat : ℤ) = b + 1 - a := Int.toNat_of_nonneg (by omega); rw [← Int.cast_natCast, h]; push_cast; ring

/-- `mun:stdlib/sums/range-from-bounds`. -/
theorem range_from_bounds (m : ℕ) (h1 : 0 < m) (x : ℕ) (h3 : (x : ℤ) < (m : ℤ)) :
    (x : ℤ) ∈ Finset.Icc (0 : ℤ) ((m : ℤ) - 1) :=
  Finset.mem_Icc.mpr ⟨by omega, by omega⟩

end LeanBridges.Sums

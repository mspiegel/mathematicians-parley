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

namespace Parley.Library

/-- A sum to n + 1 is the sum to n and the last term, where the range is
not empty. -/
theorem sum_Icc_succ_top {M : Type*} [AddCommMonoid M] {a n : ℤ} (h : a ≤ n + 1)
    (t : ℤ → M) :
    ∑ k ∈ Finset.Icc a (n + 1), t k = ∑ k ∈ Finset.Icc a n, t k + t (n + 1) := by
  have split : Finset.Icc a (n + 1) = insert (n + 1) (Finset.Icc a n) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [split, Finset.sum_insert (by simp), add_comm]

end Parley.Library

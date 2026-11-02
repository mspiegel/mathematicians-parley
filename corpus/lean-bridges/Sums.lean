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

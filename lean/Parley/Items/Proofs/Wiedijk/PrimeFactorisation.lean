module

public import Tactics

/-! Written from proofs/wiedijk/prime-factorisation.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.PrimeFactorisation

theorem def_product_of_primes (m : ℂ) :
    (∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (m = (∏ i ∈ Finset.Icc (1 : ℤ) k, ((f i : ℂ) : ℂ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat)))) ↔ (∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (m = (∏ i ∈ Finset.Icc (1 : ℤ) k, ((f i : ℂ) : ℂ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat)))) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.PrimeFactorisation

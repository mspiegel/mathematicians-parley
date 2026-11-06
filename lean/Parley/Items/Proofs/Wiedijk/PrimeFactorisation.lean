module

public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs

/-! Written from proofs/wiedijk/prime-factorisation.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.PrimeFactorisation

theorem def_product_of_primes (m : ℂ) :
    (∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (m = (∏ i ∈ Finset.Icc (1 : ℤ) k, ((f i : ℂ) : ℂ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat)))) ↔ (∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (m = (∏ i ∈ Finset.Icc (1 : ℤ) k, ((f i : ℂ) : ℂ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat)))) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.PrimeFactorisation

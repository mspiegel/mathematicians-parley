module

public import Tactics

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.PythagoreanTriples

theorem def_euclid_hypotenuse {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (b : K) (c : K) :
    (∃ k : ℤ, 0 < k ∧ (∃ m : ℤ, 0 < m ∧ (∃ n : ℤ, 0 < n ∧ (c = (k : K) * ((m : K) ^ 2 + (n : K) ^ 2) ∧ ({a, b} : Set K) = ({(k : K) * ((m : K) ^ 2 - (n : K) ^ 2), 2 * (k : K) * (m : K) * (n : K)} : Set K))))) ↔ (∃ k : ℤ, 0 < k ∧ (∃ m : ℤ, 0 < m ∧ (∃ n : ℤ, 0 < n ∧ (c = (k : K) * ((m : K) ^ 2 + (n : K) ^ 2) ∧ ({a, b} : Set K) = ({(k : K) * ((m : K) ^ 2 - (n : K) ^ 2), 2 * (k : K) * (m : K) * (n : K)} : Set K))))) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.PythagoreanTriples

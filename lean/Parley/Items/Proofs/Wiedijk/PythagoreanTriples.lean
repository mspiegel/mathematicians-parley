module

public import Tactics

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.PythagoreanTriples

theorem def_euclid_hypotenuse (a : ℂ) (b : ℂ) (c : ℂ) :
    (∃ k : ℕ, 0 < k ∧ (∃ m : ℕ, 0 < m ∧ (∃ n : ℕ, 0 < n ∧ (c = (k : ℂ) * ((m : ℂ) ^ 2 + (n : ℂ) ^ 2) ∧ ({a, b} : Set ℂ) = ({(k : ℂ) * ((m : ℂ) ^ 2 - (n : ℂ) ^ 2), 2 * (k : ℂ) * (m : ℂ) * (n : ℂ)} : Set ℂ))))) ↔ (∃ k : ℕ, 0 < k ∧ (∃ m : ℕ, 0 < m ∧ (∃ n : ℕ, 0 < n ∧ (c = (k : ℂ) * ((m : ℂ) ^ 2 + (n : ℂ) ^ 2) ∧ ({a, b} : Set ℂ) = ({(k : ℂ) * ((m : ℂ) ^ 2 - (n : ℂ) ^ 2), 2 * (k : ℂ) * (m : ℂ) * (n : ℂ)} : Set ℂ))))) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.PythagoreanTriples

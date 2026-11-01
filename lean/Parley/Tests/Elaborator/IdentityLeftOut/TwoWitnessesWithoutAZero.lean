module

public import Parley.Library

/-! Written from tests/elaborator/identity-left-out.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.IdentityLeftOut.TwoWitnessesWithoutAZero

theorem two_witnesses_without_a_zero (A : ℤ) (N : ℤ) (k : ℤ) (m : ℤ) (H5 : k * N = A + m) :
    (∃ p : ℤ, ∃ q : ℤ, p * N + 0 = A + q) := by
  -- 1. exhibit, from H5
  have s1 : ∃ p : ℤ, ∃ q : ℤ, p * N + 0 = A + q := ⟨k, m, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.IdentityLeftOut.TwoWitnessesWithoutAZero

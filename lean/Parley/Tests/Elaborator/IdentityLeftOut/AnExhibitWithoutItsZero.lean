module

public import Parley.Library

/-! Written from tests/elaborator/identity-left-out.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.IdentityLeftOut.AnExhibitWithoutItsZero

theorem an_exhibit_without_its_zero (A : ℤ) (N : ℕ) (hH2 : 0 < N) (k : ℤ) (hH4 : k * (N : ℤ) = A) :
    (∃ q : ℤ, q * (N : ℤ) + 0 = A) := by
  -- 1. exhibit, from H4
  have s1 : ∃ q : ℤ, q * (N : ℤ) + 0 = A := ⟨k, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.IdentityLeftOut.AnExhibitWithoutItsZero

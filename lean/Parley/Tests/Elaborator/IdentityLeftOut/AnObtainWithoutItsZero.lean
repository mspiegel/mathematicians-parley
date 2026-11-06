module

public import Tactics
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/identity-left-out.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.IdentityLeftOut.AnObtainWithoutItsZero

theorem an_obtain_without_its_zero (A : ℤ) (N : ℤ) (hH2 : 0 < N) (hH3 : ∃ q : ℤ, q * N + 0 = A) :
    (∃ k : ℤ, k * N = A) := by
  -- 1. obtain q from H3
  obtain ⟨q, s1⟩ := hH3
  -- 2. exhibit, from 1
  have s2 : ∃ k : ℤ, k * N = A := ⟨q, by parley_side⟩
  all_goals exact s2

end Parley.Tests.Elaborator.IdentityLeftOut.AnObtainWithoutItsZero

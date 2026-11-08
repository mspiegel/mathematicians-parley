module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/identity-left-out.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.IdentityLeftOut.AnObtainWithoutItsZero

theorem an_obtain_without_its_zero (A : ℤ) (N : ℤ) (hH2 : 0 < N) (hH3 : ∃ q : ℤ, q * N + 0 = A) :
    (∃ k : ℤ, k * N = A) := by
  -- 1. obtain q from H3
  obtain ⟨q, s1_obtained⟩ := hH3
  have s1 : q * N = A := by simpa only [add_zero] using s1_obtained
  -- 2. exhibit, from 1
  exact ⟨q, s1⟩

end Parley.Tests.Elaborator.IdentityLeftOut.AnObtainWithoutItsZero

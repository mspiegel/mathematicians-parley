module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/identity-left-out.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.IdentityLeftOut.TwoWitnessesWithoutAZero

theorem two_witnesses_without_a_zero (A : ℤ) (N : ℤ) (k : ℤ) (m : ℤ) (hH5 : k * N = A + m) :
    (∃ p : ℤ, ∃ q : ℤ, p * N + 0 = A + q) := by
  -- 1. exhibit, from H5
  exact ⟨k, m, by simpa only [add_zero] using hH5⟩

end Parley.Tests.Elaborator.IdentityLeftOut.TwoWitnessesWithoutAZero

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

namespace Parley.Tests.Elaborator.IdentityLeftOut.AnExhibitWithoutItsZero

theorem an_exhibit_without_its_zero (A : ℤ) (N : ℤ) (hH2 : 0 < N) (k : ℤ) (hH4 : k * N = A) :
    (∃ q : ℤ, q * N + 0 = A) := by
  -- 1. exhibit, from H4
  exact ⟨k, by simpa only [add_zero] using hH4⟩

end Parley.Tests.Elaborator.IdentityLeftOut.AnExhibitWithoutItsZero

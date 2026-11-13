module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/identity-left-out.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.IdentityLeftOut.AnExhibitWithoutItsZero

theorem an_exhibit_without_its_zero (A : ℤ) (N : ℤ) (hH2 : 0 < N) (k : ℤ) (hH4 : k * N = A) :
    (∃ q : ℤ, q * N + 0 = A) := by
  -- 1. exhibit, from H4
  exact ⟨k, by simpa only [add_zero] using hH4⟩

end Parley.Tests.Elaborator.IdentityLeftOut.AnExhibitWithoutItsZero

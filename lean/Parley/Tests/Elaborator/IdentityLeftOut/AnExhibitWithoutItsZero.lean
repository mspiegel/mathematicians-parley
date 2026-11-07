module

public import Tactics
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
  have s1 : ∃ q : ℤ, q * N + 0 = A := ⟨k, by parley_side⟩
  all_goals exact s1

end Parley.Tests.Elaborator.IdentityLeftOut.AnExhibitWithoutItsZero

module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/a-named-term-is-a-number.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANamedTermIsANumber.AnOddSquareOverEight

theorem an_odd_square_over_eight (N : ℤ) :
    ((2 * (N : ℚ) + 1) ^ 2 - 1) / 8 = (N : ℚ) * ((N : ℚ) + 1) / 2 := by
  set M : ℤ := 2 * N + 1 with hD1
  -- 1. algebra, from D1
  have s1 : ((M : ℚ) ^ 2 - 1) / 8 = (N : ℚ) * ((N : ℚ) + 1) / 2 := by
    try simp only [hD1] at *
    try push_cast at *
    parley_ring
  (have h := s1; rw [hD1] at h; push_cast at h ⊢; all_goals exact h)

end Parley.Tests.Elaborator.ANamedTermIsANumber.AnOddSquareOverEight

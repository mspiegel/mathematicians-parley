module

public import AlgebraTactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/a-named-term-is-a-number.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANamedTermIsANumber.ANamedTermIsANumber

theorem a_named_term_is_a_number (N : ℤ) :
    2 * N + 1 - 1 = 2 * N := by
  set M : ℤ := 2 * N + 1 with hD1
  -- 1. algebra, from D1
  try simp only [hD1] at ⊢
  try push_cast at ⊢
  parley_ring

end Parley.Tests.Elaborator.ANamedTermIsANumber.ANamedTermIsANumber

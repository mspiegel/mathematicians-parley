module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/listed-numerals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedNumerals.AValueWrittenTwice

theorem a_value_written_twice :
    (({(2 : ℤ), (3 : ℤ), (2 : ℤ)} : Set ℤ).ncard : ℤ) = 2 := by
  -- 1. inspection
  simp [Set.ncard_insert_of_notMem, Set.ncard_singleton]

end Parley.Tests.Elaborator.ListedNumerals.AValueWrittenTwice

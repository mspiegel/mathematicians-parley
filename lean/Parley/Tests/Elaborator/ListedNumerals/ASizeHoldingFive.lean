module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/listed-numerals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedNumerals.ASizeHoldingFive

theorem a_size_holding_five :
    (({(1 : ℤ), (5 : ℤ), (9 : ℤ)} : Set ℤ).ncard : ℤ) = 3 := by
  -- 1. inspection
  simp [Set.ncard_insert_of_notMem, Set.ncard_singleton]

end Parley.Tests.Elaborator.ListedNumerals.ASizeHoldingFive

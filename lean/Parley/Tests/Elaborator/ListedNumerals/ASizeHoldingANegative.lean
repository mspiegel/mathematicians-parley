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

namespace Parley.Tests.Elaborator.ListedNumerals.ASizeHoldingANegative

theorem a_size_holding_a_negative :
    (({(-2 : ℤ), (0 : ℤ), (3 : ℤ)} : Set ℤ).ncard : ℤ) = 3 := by
  -- 1. inspection
  parley_set_side

end Parley.Tests.Elaborator.ListedNumerals.ASizeHoldingANegative

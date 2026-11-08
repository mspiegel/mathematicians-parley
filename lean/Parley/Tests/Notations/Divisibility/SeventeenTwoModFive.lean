module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.ModEq

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.SeventeenTwoModFive

theorem seventeen_two_mod_five :
    (17 : ℤ) ≡ (2 : ℤ) [ZMOD (5 : ℤ)] := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Divisibility.SeventeenTwoModFive

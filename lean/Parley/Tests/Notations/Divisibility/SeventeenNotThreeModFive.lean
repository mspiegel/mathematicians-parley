module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.ModEq

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.SeventeenNotThreeModFive

theorem seventeen_not_three_mod_five :
    ¬ (17 : ℤ) ≡ (3 : ℤ) [ZMOD (5 : ℤ)] := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Divisibility.SeventeenNotThreeModFive

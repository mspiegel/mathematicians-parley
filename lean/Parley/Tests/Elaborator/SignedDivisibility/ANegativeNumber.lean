module

public import ArithTactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.ANegativeNumber

theorem a_negative_number :
    (2 : ℤ) ∣ (-8 : ℤ) := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Elaborator.SignedDivisibility.ANegativeNumber

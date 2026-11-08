module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Parity

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.ANegativeEven

theorem a_negative_even :
    Even (-6 : ℤ) := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Elaborator.SignedDivisibility.ANegativeEven

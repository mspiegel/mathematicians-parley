module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Parity

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.OneIsNotEven

theorem one_is_not_even :
    ¬ Even (1 : ℤ) := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Divisibility.OneIsNotEven

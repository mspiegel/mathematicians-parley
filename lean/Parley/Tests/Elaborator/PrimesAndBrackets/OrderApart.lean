module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/primes-and-brackets.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PrimesAndBrackets.OrderApart

theorem order_apart (a : ℝ) (b : ℝ) (hH3 : a < b) :
    b - a ≠ 0 := by
  -- 1. inequalities
  linarith only [hH3]

end Parley.Tests.Elaborator.PrimesAndBrackets.OrderApart

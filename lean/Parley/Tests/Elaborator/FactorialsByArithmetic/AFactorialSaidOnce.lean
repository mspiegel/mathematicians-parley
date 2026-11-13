module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
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

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialSaidOnce

theorem a_factorial_said_once (x : ℝ) :
    x * (LeanBridges.Counting.factorial (0 : ℤ) : ℝ) = (LeanBridges.Counting.factorial (0 : ℤ) : ℝ) * x := by
  -- 1. algebra
  parley_ring

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialSaidOnce

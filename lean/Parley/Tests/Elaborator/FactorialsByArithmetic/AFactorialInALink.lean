module

public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialInALink

theorem a_factorial_in_a_link (x : ℝ) (hH2 : x = 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℝ)) :
    x = 1 - 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℝ) := by
  -- 1. calculation
  calc x = 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℝ) := hH2
    _ = 1 - 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℝ) := by norm_num

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialInALink

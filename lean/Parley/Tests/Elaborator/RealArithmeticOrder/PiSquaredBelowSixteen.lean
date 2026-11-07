module

public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.PiSquaredBelowSixteen

theorem pi_squared_below_sixteen :
    Real.pi ^ 2 < 16 := by
  -- 1. real arithmetic
  have s1 : Real.pi ^ 2 < 16 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.PiSquaredBelowSixteen

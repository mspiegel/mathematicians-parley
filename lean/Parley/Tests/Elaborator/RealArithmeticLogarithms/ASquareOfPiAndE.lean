module

public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ASquareOfPiAndE

theorem a_square_of_pi_and_e :
    (Real.pi + Real.exp 1) ^ 2 = Real.pi ^ 2 + 2 * Real.pi * Real.exp 1 + Real.exp 1 ^ 2 := by
  -- 1. real arithmetic
  have s1 : (Real.pi + Real.exp 1) ^ 2 = Real.pi ^ 2 + 2 * Real.pi * Real.exp 1 + Real.exp 1 ^ 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ASquareOfPiAndE

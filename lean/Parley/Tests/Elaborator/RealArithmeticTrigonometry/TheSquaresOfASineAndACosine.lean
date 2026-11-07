module

public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.TheSquaresOfASineAndACosine

theorem the_squares_of_a_sine_and_a_cosine :
    Real.sin (Real.pi / 6) ^ 2 + Real.cos (Real.pi / 6) ^ 2 = 1 := by
  -- 1. real arithmetic
  have s1 : Real.sin (Real.pi / 6) ^ 2 + Real.cos (Real.pi / 6) ^ 2 = 1 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.TheSquaresOfASineAndACosine

module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineOfASixthOfPi

theorem a_sine_of_a_sixth_of_pi :
    Real.sin (Real.pi / 6) = 1 / 2 := by
  -- 1. real arithmetic
  have hv1 : Real.sin (Real.pi / 6) = 1 / 2 := by rw [congrArg Real.sin (show Real.pi / 6 = Real.pi / 6 by ring1), Real.sin_pi_div_six]
  linear_combination hv1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineOfASixthOfPi

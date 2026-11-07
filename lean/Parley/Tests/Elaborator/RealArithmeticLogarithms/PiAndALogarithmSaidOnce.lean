module

public import AlgebraTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.PiAndALogarithmSaidOnce

theorem pi_and_a_logarithm_said_once (a : ℝ) :
    a * Real.pi + Real.log (2 : ℝ) * a = (Real.pi + Real.log (2 : ℝ)) * a := by
  -- 1. algebra
  have s1 : a * Real.pi + Real.log (2 : ℝ) * a = (Real.pi + Real.log (2 : ℝ)) * a := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.PiAndALogarithmSaidOnce

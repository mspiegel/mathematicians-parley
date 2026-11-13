module

public import AlgebraTactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
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

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.PiAndALogarithmSaidOnce

theorem pi_and_a_logarithm_said_once (a : ℝ) :
    a * Real.pi + Real.log (2 : ℝ) * a = (Real.pi + Real.log (2 : ℝ)) * a := by
  -- 1. algebra
  parley_ring

end Parley.Tests.Elaborator.RealArithmeticLogarithms.PiAndALogarithmSaidOnce

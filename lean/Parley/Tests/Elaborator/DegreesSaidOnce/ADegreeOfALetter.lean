module

public import Mathlib.Algebra.Order.Field.Basic
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
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/degrees-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DegreesSaidOnce.ADegreeOfALetter

theorem a_degree_of_a_letter (x : ℝ) :
    x * Real.pi / 180 + (180 : ℝ) * Real.pi / 180 = (180 : ℝ) * Real.pi / 180 + x * Real.pi / 180 := by
  -- 1. algebra
  ring1

end Parley.Tests.Elaborator.DegreesSaidOnce.ADegreeOfALetter

module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/bounds-from-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BoundsFromCited.AnEquationFromADifferenceWithABoundUncited

theorem an_equation_from_a_difference_with_a_bound_uncited (a : ℝ) (b : ℝ) (hH3 : a ≤ b) (hH4 : b - a = 0) :
    a = b := by
  -- 1. inequalities
  linarith only [hH4]

end Parley.Tests.Elaborator.BoundsFromCited.AnEquationFromADifferenceWithABoundUncited

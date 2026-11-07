module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedFillingAnItemHypothesis

theorem an_equation_turned_filling_an_item_hypothesis (x : ℝ) (hH2 : 0 = x ^ 2) :
    x = 0 := by
  -- 1. mun:square-zero, from H2
  have s1 : x = 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_zero (x := x) (by parley_side))
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedFillingAnItemHypothesis

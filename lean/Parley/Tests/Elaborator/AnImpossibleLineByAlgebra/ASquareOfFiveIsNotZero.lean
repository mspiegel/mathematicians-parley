module

public import ArithTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core

/-! Written from tests/elaborator/an-impossible-line-by-algebra.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ASquareOfFiveIsNotZero

theorem a_square_of_five_is_not_zero (x : ℝ) (hH2 : x ^ 2 = 5) :
    x ≠ 0 := by
  -- 1. contradiction
  have s1 : x ≠ 0 := by
    by_contra hc_hS
    have hS : x = 0 := by parley_suppose hc_hS
    -- 1.1. algebra, from H2, S
    have s1_1 : (5 : ℝ) = 0 := by linear_combination (norm := parley_norm) (-1) * hH2 + (x) * hS
    exact absurd s1_1 (by norm_num)
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ASquareOfFiveIsNotZero

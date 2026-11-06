module

public import ArithTactics
public import RealTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination

/-! Written from tests/elaborator/an-impossible-line-by-algebra.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ANumberEqualToARootIsNotOne

theorem a_number_equal_to_a_root_is_not_one (x : ℝ) (hH2 : x = Real.sqrt (2 : ℝ)) :
    x ≠ 1 := by
  -- 1. contradiction
  have s1 : x ≠ 1 := by
    by_contra hc_hS
    have hS : x = 1 := by parley_suppose hc_hS
    -- 1.1. algebra, from H2, S
    have s1_1 : Real.sqrt (2 : ℝ) - 1 = 0 := by linear_combination (norm := parley_norm) (-1) * hH2 + hS
    exact absurd s1_1 (by parley_real)
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ANumberEqualToARootIsNotOne

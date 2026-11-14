module

public import RealTactics
public import Mathlib.Analysis.Real.Sqrt
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
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/an-impossible-line-by-algebra.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ANumberEqualToARootIsNotOne

theorem a_number_equal_to_a_root_is_not_one (x : ℝ) (hH2 : x = Real.sqrt (2 : ℝ)) :
    x ≠ 1 := by
  -- 1. contradiction
  intro hS
  -- 1.1. algebra, from H2, S
  have s1_1 : Real.sqrt (2 : ℝ) - 1 = 0 := by linear_combination (-1) * hH2 + hS
  exact absurd s1_1 (by parley_real)

end Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ANumberEqualToARootIsNotOne

module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/an-impossible-line-by-algebra.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ASquareOfFiveIsNotZero

theorem a_square_of_five_is_not_zero (x : ℝ) (hH2 : x ^ 2 = 5) :
    x ≠ 0 := by
  -- 1. contradiction
  intro hS
  -- 1.1. algebra, from H2, S
  have s1_1 : (5 : ℝ) = 0 := by linear_combination (norm := parley_norm) (-1) * hH2 + (x) * hS
  exact absurd s1_1 (by norm_num)

end Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ASquareOfFiveIsNotZero

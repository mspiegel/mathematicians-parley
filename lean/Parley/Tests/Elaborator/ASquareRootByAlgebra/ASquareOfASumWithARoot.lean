module

public import ArithTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-square-root-by-algebra.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASquareRootByAlgebra.ASquareOfASumWithARoot

theorem a_square_of_a_sum_with_a_root (a : ℝ) :
    (a + Real.sqrt (2 : ℝ)) ^ 2 = a ^ 2 + 2 * Real.sqrt (2 : ℝ) * a + 2 := by
  -- 1. def:sqrt x := 2
  have r22_1 : (2 : ℤ) ≥ 0 := by parley_arith
  have s1a : Real.sqrt (2 : ℝ) ≥ 0 := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side))
  have s1b : Real.sqrt (2 : ℝ) ^ 2 = 2 := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side))
  -- 2. algebra, from 1
  linear_combination (norm := parley_norm) s1b

end Parley.Tests.Elaborator.ASquareRootByAlgebra.ASquareOfASumWithARoot

module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/textbook-exercise-shapes-two.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapesTwo.ARootInABound

theorem a_root_in_a_bound (a : ℝ) (hH2 : a ≥ 0) (hH3 : ¬ a ≥ 2 * Real.sqrt a) :
    a < 2 * Real.sqrt a := by
  -- 1. def:sqrt x := a, from H2
  have s1a : Real.sqrt a ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) hH2)
  have s1b : Real.sqrt a ^ 2 = a := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) hH2)
  -- 2. inequalities, from H3, 1
  linarith only [hH3]

end Parley.Tests.Elaborator.TextbookExerciseShapesTwo.ARootInABound

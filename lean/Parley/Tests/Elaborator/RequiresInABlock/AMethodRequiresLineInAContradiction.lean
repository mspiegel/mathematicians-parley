module

public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/requires-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RequiresInABlock.AMethodRequiresLineInAContradiction

theorem a_method_requires_line_in_a_contradiction (A : ℝ) (B : ℝ) (hH3 : 0 ≤ A) (hH4 : 0 ≤ B) (hH5 : A < B) :
    A ^ 2 < B ^ 2 := by
  -- 1. contradiction
  by_contra hS1
  -- 1.1. inequalities, from S1
  have s1_1 : B ^ 2 ≤ A ^ 2 := by linarith only [hS1]
  -- 1.2. mun:square-less x := A, y := B, from H5
  have r46_1 : A ≥ 0 := by linarith only [hH3]
  have r46_2 : B ≥ 0 := by exact hH4
  have s1_2 : A ^ 2 < B ^ 2 := by exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) r46_1 r46_2)).mp hH5
  -- 1.3. inequalities, from 1.1
  have s1_3 : ¬ A ^ 2 < B ^ 2 := by linarith only [s1_1]
  exact s1_3 s1_2

end Parley.Tests.Elaborator.RequiresInABlock.AMethodRequiresLineInAContradiction

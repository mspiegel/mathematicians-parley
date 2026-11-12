module

public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic

/-! Written from tests/elaborator/textbook-exercise-shapes-two.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapesTwo.AContradictionEndingInCases

theorem a_contradiction_ending_in_cases (x : ℝ) (hH2 : x > 2 ∨ x > 1) :
    x > 0 := by
  -- 1. contradiction
  by_contra hS
  -- 1.1. cases, from H2
  have s1_1 : x > 0 := by
    rcases hH2 with hC1 | hC2
    · skip
      -- 1.1.1. inequalities, from C1
      linarith only [hC1]
    · skip
      -- 1.1.2. inequalities, from C2
      linarith only [hC2]
  exact hS s1_1

end Parley.Tests.Elaborator.TextbookExerciseShapesTwo.AContradictionEndingInCases

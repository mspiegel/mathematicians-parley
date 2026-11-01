module

public import Parley.Library

/-! Written from tests/elaborator/textbook-exercise-shapes-two.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapesTwo.AContradictionEndingInCases

theorem a_contradiction_ending_in_cases (x : ℝ) (H2 : x > 2 ∨ x > 1) :
    x > 0 := by
  -- 1. contradiction
  have s1 : x > 0 := by
    by_contra hc_S
    have S : ¬ x > 0 := by parley_suppose hc_S
    -- 1.1. cases, from H2
    have s1_1 : x > 0 := by
      rcases H2 with C1 | C2
      · skip
        -- 1.1.1. inequalities, from C1
        have s1_1_1 : x > 0 := by parley_side
        parley_side
      · skip
        -- 1.1.2. inequalities, from C2
        have s1_1_2 : x > 0 := by parley_side
        parley_side
    parley_side
  parley_side

end Parley.Tests.Elaborator.TextbookExerciseShapesTwo.AContradictionEndingInCases

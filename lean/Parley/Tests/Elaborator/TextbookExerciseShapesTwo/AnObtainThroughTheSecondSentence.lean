module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/textbook-exercise-shapes-two.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapesTwo.AnObtainThroughTheSecondSentence

theorem an_obtain_through_the_second_sentence (a : ℤ) (b : ℤ) (hH3 : Odd a ∧ Odd b) :
    (∃ j : ℤ, b = 2 * j + 1) := by
  -- 1. obtain j: def:odd n := b, from H3
  obtain ⟨j, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := b))).mp (by parley_side)
  -- 2. exhibit, from 1
  have s2 : ∃ j : ℤ, b = 2 * j + 1 := ⟨j, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.TextbookExerciseShapesTwo.AnObtainThroughTheSecondSentence

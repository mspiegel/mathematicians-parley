module

public import Tactics
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/textbook-exercise-shapes-two.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapesTwo.AnObtainThroughTheSecondSentence

theorem an_obtain_through_the_second_sentence (a : ℤ) (b : ℤ) (hH3 : Odd a ∧ Odd b) :
    (∃ j : ℤ, b = 2 * j + 1) := by
  -- 1. obtain j: def:odd n := b, from H3
  obtain ⟨j, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := b))).mp hH3.2
  -- 2. exhibit, from 1
  exact ⟨j, s1⟩

end Parley.Tests.Elaborator.TextbookExerciseShapesTwo.AnObtainThroughTheSecondSentence

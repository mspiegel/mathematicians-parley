module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineObtainedFrom

theorem a_for_all_line_obtained_from (hH1 : ∀ x : ℤ, ∃ k : ℤ, x = 2 * k) :
    (∀ y : ℤ, ∃ j : ℤ, y = 2 * j) := by
  -- 1. proof
  intro y
  -- 1.1. obtain k from H1
  obtain ⟨k, s1_1⟩ := (hH1 y)
  -- 1.2. exhibit, from 1.1
  exact ⟨k, s1_1⟩

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineObtainedFrom

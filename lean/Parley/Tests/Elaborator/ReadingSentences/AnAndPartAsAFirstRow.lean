module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartAsAFirstRow

theorem an_and_part_as_a_first_row (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b > 0) :
    b + 1 > 1 := by
  -- 1. inequalities
  linarith only [hH3.2]

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartAsAFirstRow

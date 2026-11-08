module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight

/-! Written from tests/elaborator/a-natural-is-at-least-one-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.ANaturalAnswersAtLeastOne

theorem a_natural_answers_at_least_one (j : ℤ) (hH1 : 0 < j) :
    0 < j := by
  -- 1. thm:at-least-one-right x := j, from H1
  exact (Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight.at_least_one_right (x := j) (by parley_side))

end Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.ANaturalAnswersAtLeastOne

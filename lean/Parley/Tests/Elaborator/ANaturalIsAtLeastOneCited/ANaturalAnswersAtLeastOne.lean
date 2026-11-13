module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight

/-! Written from tests/elaborator/a-natural-is-at-least-one-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.ANaturalAnswersAtLeastOne

theorem a_natural_answers_at_least_one (j : ℤ) (hH1 : 0 < j) :
    0 < j := by
  -- 1. thm:at-least-one-right x := j, from H1
  exact (Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight.at_least_one_right (x := j) hH1)

end Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.ANaturalAnswersAtLeastOne

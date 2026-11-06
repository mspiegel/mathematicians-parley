module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight

/-! Written from tests/elaborator/a-natural-is-at-least-one-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.ANaturalAnswersAtLeastOne

theorem a_natural_answers_at_least_one (j : ℤ) (hH1 : 0 < j) :
    0 < j := by
  -- 1. thm:at-least-one-right x := j, from H1
  have s1 : 0 < j := by first | linarith [(Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight.at_least_one_right (x := j) (by parley_side))] | (have h := (Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight.at_least_one_right (x := j) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight.at_least_one_right (x := j) (by parley_side)) | (have h := (Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight.at_least_one_right (x := j) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.ANaturalAnswersAtLeastOne

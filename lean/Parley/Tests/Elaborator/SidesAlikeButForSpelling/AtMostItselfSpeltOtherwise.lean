module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/sides-alike-but-for-spelling.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SidesAlikeButForSpelling.AtMostItselfSpeltOtherwise

theorem at_most_itself_spelt_otherwise (A : ℝ) (B : ℝ) :
    B + (A - B) ≤ A := by
  -- 1. inequalities
  have s1 : B + (A - B) ≤ A := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.SidesAlikeButForSpelling.AtMostItselfSpeltOtherwise

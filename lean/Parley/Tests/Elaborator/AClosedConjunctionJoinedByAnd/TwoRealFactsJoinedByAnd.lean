module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/a-closed-conjunction-joined-by-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoRealFactsJoinedByAnd

theorem two_real_facts_joined_by_and :
    (Real.sqrt (4 : ℝ) = 2 ∧ Real.pi > 3) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (4 : ℝ) = 2 ∧ Real.pi > 3 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoRealFactsJoinedByAnd

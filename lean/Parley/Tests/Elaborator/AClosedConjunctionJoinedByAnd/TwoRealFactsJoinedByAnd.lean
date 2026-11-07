module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.RealSqrt

/-! Written from tests/elaborator/a-closed-conjunction-joined-by-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoRealFactsJoinedByAnd

theorem two_real_facts_joined_by_and :
    (Real.sqrt (4 : ℝ) = 2 ∧ Real.pi > 3) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (4 : ℝ) = 2 ∧ Real.pi > 3 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoRealFactsJoinedByAnd

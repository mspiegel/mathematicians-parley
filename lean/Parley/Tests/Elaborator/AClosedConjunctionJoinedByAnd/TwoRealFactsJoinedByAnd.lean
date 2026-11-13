module

public import RealTactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-closed-conjunction-joined-by-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoRealFactsJoinedByAnd

theorem two_real_facts_joined_by_and :
    (Real.sqrt (4 : ℝ) = 2 ∧ Real.pi > 3) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (4 : ℝ) = 2 ∧ Real.pi > 3 := by parley_real
  exact ⟨(s1).1, (s1).2⟩

end Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoRealFactsJoinedByAnd

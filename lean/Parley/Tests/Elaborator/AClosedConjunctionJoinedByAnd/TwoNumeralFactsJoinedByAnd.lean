module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-closed-conjunction-joined-by-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoNumeralFactsJoinedByAnd

theorem two_numeral_facts_joined_by_and :
    ((2 * 3 : ℤ) = 6 ∧ (1 : ℤ) < 2) := by
  -- 1. arithmetic
  have s1 : (2 * 3 : ℤ) = 6 ∧ (1 : ℤ) < 2 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoNumeralFactsJoinedByAnd

module

public import ArithTactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-closed-conjunction-joined-by-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoNumeralFactsJoinedByAnd

theorem two_numeral_facts_joined_by_and :
    ((2 * 3 : ℤ) = 6 ∧ (1 : ℤ) < 2) := by
  -- 1. arithmetic
  have s1 : (2 * 3 : ℤ) = 6 ∧ (1 : ℤ) < 2 := by parley_arith
  exact ⟨(s1).1, (s1).2⟩

end Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoNumeralFactsJoinedByAnd

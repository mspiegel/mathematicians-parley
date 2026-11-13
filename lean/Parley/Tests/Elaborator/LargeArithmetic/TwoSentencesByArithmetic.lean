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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.TwoSentencesByArithmetic

theorem two_sentences_by_arithmetic :
    (2 + 2 : ℤ) = 4 ∧ (3 * 3 : ℤ) = 9 := by
  -- 1. arithmetic
  have s1a : (2 + 2 : ℤ) = 4 := by parley_arith
  have s1b : (3 * 3 : ℤ) = 9 := by parley_arith
  exact ⟨s1a, s1b⟩

end Parley.Tests.Elaborator.LargeArithmetic.TwoSentencesByArithmetic

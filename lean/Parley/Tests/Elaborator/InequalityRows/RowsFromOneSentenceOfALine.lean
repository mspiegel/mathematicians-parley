module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.RowsFromOneSentenceOfALine

theorem rows_from_one_sentence_of_a_line (p : ℝ) (q : ℝ) (hH3 : 0 < q ∧ q < 1) :
    2 * q < 2 ∧ p / q * q = p := by
  -- 1. inequalities
  have s1 : 2 * q < 2 := by parley_order
  -- 2. algebra
  have r67_1 : 0 ≠ q := by parley_side
  have s2 : p / q * q = p := by parley_ring
  -- 3. join 1, 2
  have s3a : 2 * q < 2 := by parley_side
  have s3b : p / q * q = p := by parley_side
  exact ⟨s3a, s3b⟩

end Parley.Tests.Elaborator.InequalityRows.RowsFromOneSentenceOfALine

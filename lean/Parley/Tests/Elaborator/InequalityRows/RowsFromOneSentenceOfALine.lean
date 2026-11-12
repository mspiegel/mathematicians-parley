module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
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
  have s1 : 2 * q < 2 := by linarith only [hH3.2]
  -- 2. algebra
  have r67_1 : 0 ≠ q := ne_of_lt (by linarith only [hH3.1])
  have s2 : p / q * q = p := by parley_ring
  -- 3. join 1, 2
  have s3a : 2 * q < 2 := s1
  have s3b : p / q * q = p := s2
  exact ⟨s3a, s3b⟩

end Parley.Tests.Elaborator.InequalityRows.RowsFromOneSentenceOfALine

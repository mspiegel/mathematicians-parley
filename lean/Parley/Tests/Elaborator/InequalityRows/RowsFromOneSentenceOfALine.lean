module

public import AlgebraTactics
public import OrderTactics
public import Tactics

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
  exact ⟨by parley_side, by parley_side⟩

end Parley.Tests.Elaborator.InequalityRows.RowsFromOneSentenceOfALine

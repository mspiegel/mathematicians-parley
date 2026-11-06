module

public import ArithTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination

/-! Written from tests/elaborator/substitute-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SubstituteRows.SubstituteRowsFromALine

theorem substitute_rows_from_a_line (x : ℝ) (y : ℝ) (hH3 : x = 3) (hH4 : x * x + x < y) :
    12 < y := by
  -- 1. substitute
  have s1 : 12 < y := by
    have c1 : x = 3 := by parley_subst hH3
    have row1 : 3 * 3 + 3 < y := by parley_subst_at c1 hH4
    have c2 : (3 * 3 + 3 : ℤ) = 12 := by parley_arith
    have c2_w : (3 * 3 + 3 : ℝ) = 12 := by have h := congrArg (fun x : ℤ => (x : ℝ)) c2; push_cast at h; linear_combination (norm := parley_norm) h
    have row2 : 12 < y := by first | parley_put_at c2_w row1 | parley_put_at c2 row1 | parley_subst_at c2_w row1 | parley_subst_at c2 row1
    exact row2
  all_goals exact s1

end Parley.Tests.Elaborator.SubstituteRows.SubstituteRowsFromALine

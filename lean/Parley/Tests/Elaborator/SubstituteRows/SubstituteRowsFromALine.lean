module

public import ArithTactics
public import NormTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/substitute-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SubstituteRows.SubstituteRowsFromALine

theorem substitute_rows_from_a_line (x : ℝ) (y : ℝ) (hH3 : x = 3) (hH4 : x * x + x < y) :
    12 < y := by
  -- 1. substitute
  have c1 : x = 3 := by (have h := congrArg (fun t : ℝ => t) hH3; push_cast at h ⊢; all_goals exact_mod_cast h)
  have row1 : 3 * 3 + 3 < y := by (have h := Eq.subst (motive := (fun t : ℝ => t * t + t < y)) c1 hH4; push_cast at h ⊢; all_goals exact_mod_cast h)
  have c2 : (3 * 3 + 3 : ℤ) = 12 := by parley_arith
  have row2 : 12 < y := by
    have e_w : (3 * 3 + 3 : ℝ) = 12 := by have h := congrArg (fun x : ℤ => (x : ℝ)) c2; push_cast at h; linear_combination (norm := parley_norm) h
    (have h := Eq.subst (motive := (fun t : ℝ => t < y)) e_w row1; push_cast at h ⊢; all_goals exact_mod_cast h)
  exact row2

end Parley.Tests.Elaborator.SubstituteRows.SubstituteRowsFromALine

module

public import NormTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnAlgebraStep

theorem a_define_read_in_an_algebra_step (a : ℝ) (b : ℝ) (hH3 : a + 1 = 2 * b) :
    a = 2 * b - 1 := by
  set e : ℝ := a + 1 with hD1
  have hD1_kind : True := by parley_side
  -- 1. substitute e = a + 1 (D1) into H3
  have s1 : e = 2 * b := by (have h := Eq.subst (motive := (fun t : ℝ => t = 2 * b)) hD1.symm hH3; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. algebra, from D1, 1
  try simp only [hD1] at *
  try push_cast at *
  linear_combination (norm := parley_norm) s1

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnAlgebraStep

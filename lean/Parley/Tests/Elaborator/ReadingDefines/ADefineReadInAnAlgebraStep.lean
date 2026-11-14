module

public import NormTactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnAlgebraStep

theorem a_define_read_in_an_algebra_step (a : ℝ) (b : ℝ) (hH3 : a + 1 = 2 * b) :
    a = 2 * b - 1 := by
  set e : ℝ := a + 1 with hD1
  -- 1. substitute e = a + 1 (D1) into H3
  have s1 : e = 2 * b := Eq.subst (motive := (fun t : ℝ => t = 2 * b)) hD1.symm hH3
  -- 2. algebra, from D1, 1
  simp only [hD1] at s1
  linear_combination (norm := parley_norm) s1

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnAlgebraStep

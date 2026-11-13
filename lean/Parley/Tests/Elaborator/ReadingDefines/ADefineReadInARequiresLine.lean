module

public import AlgebraTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
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
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInARequiresLine

theorem a_define_read_in_a_requires_line (a : ℝ) (hH2 : a + 1 ≠ 0) :
    (a + 1) / (a + 1) = 1 := by
  set e : ℝ := a + 1 with hD1
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e ≠ 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t ≠ 0)) hD1.symm hH2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. algebra
  have r56_1 : a + 1 ≠ 0 := by exact s1
  parley_ring

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInARequiresLine

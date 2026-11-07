module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInARequiresLine

theorem a_define_read_in_a_requires_line (a : ℝ) (hH2 : a + 1 ≠ 0) :
    (a + 1) / (a + 1) = 1 := by
  set e : ℝ := a + 1 with hD1
  have hD1_kind : True := by parley_side
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e ≠ 0 := by parley_subst_at hD1 hH2
  -- 2. algebra
  have r56_1 : a + 1 ≠ 0 := by parley_side
  have s2 : (a + 1) / (a + 1) = 1 := by parley_ring
  all_goals exact s2

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInARequiresLine

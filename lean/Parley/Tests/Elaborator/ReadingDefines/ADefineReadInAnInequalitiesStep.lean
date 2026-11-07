module

public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnInequalitiesStep

theorem a_define_read_in_an_inequalities_step (a : ℝ) (hH2 : a + 1 > 0) :
    a + 1 > -1 := by
  set e : ℝ := a + 1 with hD1
  have hD1_kind : True := by parley_side
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e > 0 := by parley_subst_at hD1 hH2
  -- 2. inequalities, from D1, 1
  have s2 : a + 1 > -1 := by parley_order
  all_goals exact s2

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnInequalitiesStep

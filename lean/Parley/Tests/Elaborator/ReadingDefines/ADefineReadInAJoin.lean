module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAJoin

theorem a_define_read_in_a_join (a : ℝ) (hH2 : a + 1 > 0) :
    a + 1 > 0 := by
  set e : ℝ := a + 1 with hD1
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e > 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t > 0)) hD1.symm hH2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. restate D1, 1
  exact s1

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAJoin

module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInACaseSplit

theorem a_define_read_in_a_case_split (a : ℝ) (hH2 : a + 1 < 0 ∨ a + 1 > 0) :
    a + 1 ≠ 0 := by
  set e : ℝ := a + 1 with hD1
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e < 0 ∨ e > 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t < 0 ∨ t > 0)) hD1.symm hH2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. cases, from D1, 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. inequalities
    exact ne_of_lt (by linarith only [hC1])
  · skip
    -- 2.2. inequalities
    exact ne_of_gt (by linarith only [hC2])

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInACaseSplit

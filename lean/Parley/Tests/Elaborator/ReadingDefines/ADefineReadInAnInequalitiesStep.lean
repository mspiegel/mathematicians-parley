module

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

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnInequalitiesStep

theorem a_define_read_in_an_inequalities_step (a : ℝ) (hH2 : a + 1 > 0) :
    a + 1 > -1 := by
  set e : ℝ := a + 1 with hD1
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e > 0 := Eq.subst (motive := (fun t : ℝ => t > 0)) hD1.symm hH2
  -- 2. inequalities, from D1, 1
  linarith only [s1, hD1]

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnInequalitiesStep

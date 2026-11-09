module

public import SubstTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnInstantiatedLine

theorem a_define_read_in_an_instantiated_line (a : ℝ) (hH2 : ∀ x : ℝ, x + (a + 1) > x) :
    2 + (a + 1) > 2 := by
  set e : ℝ := a + 1 with hD1
  have hD1_kind : True := by parley_side
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : ∀ x : ℝ, x + e > x := by intro x; parley_subst_at hD1 hH2
  -- 2. instantiate x := 2 in line 1, from D1
  linarith [(s1 (2 : ℝ))]

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnInstantiatedLine

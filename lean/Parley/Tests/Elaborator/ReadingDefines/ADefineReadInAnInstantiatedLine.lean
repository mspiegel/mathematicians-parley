module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnInstantiatedLine

theorem a_define_read_in_an_instantiated_line (a : ℝ) (hH2 : ∀ x : ℝ, x + (a + 1) > x) :
    2 + (a + 1) > 2 := by
  set e : ℝ := a + 1 with hD1
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : ∀ x : ℝ, x + e > x := by (have h := Eq.subst (motive := (fun t : ℝ => ∀ x : ℝ, x + t > x)) hD1.symm hH2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. instantiate x := 2 in line 1, from D1
  exact (s1 (2 : ℝ))

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnInstantiatedLine

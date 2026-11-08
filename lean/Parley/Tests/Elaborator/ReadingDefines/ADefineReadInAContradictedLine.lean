module

public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAContradictedLine

theorem a_define_read_in_a_contradicted_line (a : ℝ) (hH2 : a + 1 ≠ 0) :
    a ≠ -1 := by
  set e : ℝ := a + 1 with hD1
  have hD1_kind : True := by parley_side
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e ≠ 0 := by parley_subst_at hD1 hH2
  -- 2. contradiction
  intro hS
  -- 2.1. algebra, from D1, S
  have s2_1 : a + 1 = 0 := by
    try simp only [hD1] at *
    try push_cast at *
    linear_combination (norm := parley_norm) hS
  exact s1 s2_1

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAContradictedLine

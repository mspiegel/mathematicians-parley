module

public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnUnfoldedDefinition

theorem a_define_read_in_an_unfolded_definition (a : ℤ) (b : ℤ) (hH3 : a + 1 = 2 * b) :
    Even (a + 1) := by
  set e : ℝ := (a : ℝ) + 1 with hD1
  have hD1_kind : True := by parley_side
  -- 1. substitute e = a + 1 (D1) into H3
  have s1 : e = 2 * (b : ℝ) := by
    have hH3_w : (a : ℝ) + 1 = 2 * (b : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) hH3; push_cast at h; linear_combination (norm := parley_norm) h
    parley_subst_at hD1 hH3_w
  -- 2. def:even n := a + 1, from D1, 1
  have s2 : Even (a + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := a + 1))).mpr ⟨b, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := a + 1))).mpr ⟨b, by parley_side⟩; parley_side)
  all_goals exact s2

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnUnfoldedDefinition

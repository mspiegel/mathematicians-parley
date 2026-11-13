module

public import NormTactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnUnfoldedDefinition

theorem a_define_read_in_an_unfolded_definition (a : ℤ) (b : ℤ) (hH3 : a + 1 = 2 * b) :
    Even (a + 1) := by
  set e : ℝ := (a : ℝ) + 1 with hD1
  -- 1. substitute e = a + 1 (D1) into H3
  have s1 : e = 2 * (b : ℝ) := by
    have hH3_w : (a : ℝ) + 1 = 2 * (b : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) hH3; push_cast at h; linear_combination (norm := parley_norm) h
    (have h := Eq.subst (motive := (fun t : ℝ => t = 2 * (b : ℝ))) hD1.symm hH3_w; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. def:even n := a + 1, from D1, 1
  exact ((Parley.Items.Stdlib.Divisibility.def_even (n := a + 1))).mpr ⟨b, by (have h := s1; simp only [hD1] at h; exact_mod_cast h)⟩

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnUnfoldedDefinition

module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnItemHypothesis

theorem a_define_read_in_an_item_hypothesis (a : ℝ) (hH2 : a + 1 > 0) :
    1 / (a + 1) > 0 := by
  set e : ℝ := a + 1 with hD1
  have hD1_kind : True := by parley_side
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e > 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t > 0)) (hD1).symm hH2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. mun:reciprocal-positive, from D1, 1
  try simp only [hD1] at *
  try push_cast at *
  exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := a + 1) (by parley_side))

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnItemHypothesis

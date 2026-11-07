module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartInARequiresLine

theorem an_and_part_in_a_requires_line (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b > 0) :
    a / b * b = a := by
  -- 1. algebra
  have r77_1 : b ≠ 0 := by parley_side
  have s1 : a / b * b = a := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartInARequiresLine

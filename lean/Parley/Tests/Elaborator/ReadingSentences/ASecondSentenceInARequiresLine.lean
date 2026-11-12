module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInARequiresLine

theorem a_second_sentence_in_a_requires_line (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b > 0) :
    a / b * b = a := by
  -- 1. algebra
  have r64_1 : b ≠ 0 := ne_of_gt (by linarith only [hH3b])
  parley_ring

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInARequiresLine

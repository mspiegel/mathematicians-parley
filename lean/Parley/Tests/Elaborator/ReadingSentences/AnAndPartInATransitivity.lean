module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartInATransitivity

theorem an_and_part_in_a_transitivity (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a = 1 ∧ b ≤ c) (hH5 : c < 0) :
    b < 0 := by
  -- 1. transitivity, from H4, H5
  exact lt_of_le_of_lt hH4.2 hH5

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartInATransitivity

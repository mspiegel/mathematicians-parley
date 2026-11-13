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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartFillingAnItem

theorem an_and_part_filling_an_item (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b = 2) :
    (b = 0 ∨ b = 2) := by
  -- 1. mun:or-right P := b = 0, Q := b = 2, from H3
  exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) hH3.2)

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartFillingAnItem

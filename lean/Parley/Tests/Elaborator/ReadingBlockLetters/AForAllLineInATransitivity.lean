module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInATransitivity

theorem a_for_all_line_in_a_transitivity (b : ℝ) (hH2 : ∀ x : ℝ, x < x + 1) :
    (∀ y : ℝ, y + 1 < b → y < b) := by
  -- 1. proof
  intro y
  intro hA1
  -- 1.1. transitivity, from H2, A1
  exact lt_trans (hH2 y) hA1

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInATransitivity

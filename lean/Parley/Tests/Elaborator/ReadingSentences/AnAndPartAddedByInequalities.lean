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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartAddedByInequalities

theorem an_and_part_added_by_inequalities (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a = 1 ∧ b > 0) (hH5 : c > 0) :
    b + c > 0 := by
  -- 1. inequalities, from H4, H5
  linarith only [hH4.2, hH5]

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartAddedByInequalities

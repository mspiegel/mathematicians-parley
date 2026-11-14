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

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartAsTheSubstitutedEquation

theorem an_and_part_as_the_substituted_equation (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b = 2) :
    a + b = a + 2 := by
  -- 1. substitute b = 2 (H3)
  exact congrArg (fun t : ℝ => a + t) hH3.2

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartAsTheSubstitutedEquation

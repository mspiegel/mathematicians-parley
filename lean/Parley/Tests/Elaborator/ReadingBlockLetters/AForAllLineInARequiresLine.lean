module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInARequiresLine

theorem a_for_all_line_in_a_requires_line (hH1 : ∀ x : ℝ, x ^ 2 + 1 ≠ 0) :
    True := by
  -- 1. proof
  -- what this block shows, Lean's types give
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInARequiresLine

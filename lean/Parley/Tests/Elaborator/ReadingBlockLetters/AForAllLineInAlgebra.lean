module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInAlgebra

theorem a_for_all_line_in_algebra (hH1 : ∀ x : ℝ, x ^ 2 = 2 * x) :
    (∀ y : ℝ, y ^ 2 + 1 = 2 * y + 1) := by
  -- 1. proof
  intro y
  -- 1.1. algebra, from H1
  linear_combination (norm := parley_norm) (hH1 y)

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInAlgebra

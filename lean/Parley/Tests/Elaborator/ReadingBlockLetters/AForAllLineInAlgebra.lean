module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInAlgebra

theorem a_for_all_line_in_algebra (hH1 : ∀ x : ℝ, x ^ 2 = 2 * x) :
    (∀ y : ℝ, y ^ 2 + 1 = 2 * y + 1) := by
  -- 1. proof
  intro y
  -- 1.1. algebra, from H1
  linear_combination (hH1 y)

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInAlgebra

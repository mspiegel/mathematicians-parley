module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineUnfoldingADefinition

theorem a_for_all_line_unfolding_a_definition (hH1 : ∀ x : ℝ, x ^ 2 ≥ 0) :
    (∀ y : ℝ, abs (y ^ 2) = y ^ 2) := by
  -- 1. proof
  intro y
  -- 1.1. def:abs x := y², from H1
  exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y ^ 2)) (hH1 y)

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineUnfoldingADefinition

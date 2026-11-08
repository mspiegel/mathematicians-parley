module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineContradicted

theorem a_for_all_line_contradicted (hH1 : ∀ x : ℝ, x ^ 2 + 1 ≠ 0) :
    (∀ y : ℝ, y ^ 2 + 1 ≠ 0) := by
  -- 1. proof
  intro y
  -- 1.1. contradiction
  intro hS
  -- 1.1.1. restate S
  have s1_1_1 : y ^ 2 + 1 = 0 := by parley_side
  exact (hH1 y) s1_1_1

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineContradicted

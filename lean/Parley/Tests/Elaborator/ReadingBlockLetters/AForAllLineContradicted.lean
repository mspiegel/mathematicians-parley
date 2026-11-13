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

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineContradicted

theorem a_for_all_line_contradicted (hH1 : ∀ x : ℝ, x ^ 2 + 1 ≠ 0) :
    (∀ y : ℝ, y ^ 2 + 1 ≠ 0) := by
  -- 1. proof
  intro y
  -- 1.1. contradiction
  intro hS
  -- 1.1.1. restate S
  have s1_1_1 : y ^ 2 + 1 = 0 := by exact hS
  exact (hH1 y) s1_1_1

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineContradicted

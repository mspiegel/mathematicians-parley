module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInstantiated

theorem a_for_all_line_instantiated (hH1 : ∀ x : ℝ, ∀ z : ℝ, x * z = z * x) :
    (∀ y : ℝ, y * 2 = 2 * y) := by
  -- 1. proof
  intro y
  -- 1.1. instantiate z := 2 in H1
  exact ((hH1 y) (2 : ℝ))

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInstantiated

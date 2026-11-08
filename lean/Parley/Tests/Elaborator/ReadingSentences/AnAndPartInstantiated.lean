module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartInstantiated

theorem an_and_part_instantiated (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ (∀ x : ℝ, x * 0 = 0)) :
    b * 0 = 0 := by
  -- 1. instantiate x := b in H3
  exact (hH3.2 b)

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartInstantiated

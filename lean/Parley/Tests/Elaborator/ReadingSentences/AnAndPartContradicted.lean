module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartContradicted

theorem an_and_part_contradicted (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b ≠ 2) :
    (b = 2 → a = 0) := by
  -- 1. proof
  intro hK1
  -- 1.1. restate K1
  have s1_1 : b = 2 := by exact hK1
  exact absurd s1_1 hH3.2

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartContradicted

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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

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

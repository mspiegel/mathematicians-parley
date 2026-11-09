module

public import NormTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor

/-! Written from tests/elaborator/a-cited-conclusion-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessorAtZero

theorem doubled_successor_at_zero :
    (2 * 1 : ℤ) = 2 * 0 + 2 := by
  -- 1. thm:doubled-successor n := 0
  linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor.doubled_successor (n := (0 : ℤ)) (by parley_side))

end Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessorAtZero

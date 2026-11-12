module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint

/-! Written from tests/elaborator/a-cited-letter-bound-in-its-own-hypothesis.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtThree

theorem positive_at_three (g : ℤ → ℝ) (hH2 : ∀ k : ℤ, 0 < k → g k > 0) :
    g 3 > 0 := by
  -- 1. thm:positive-at-a-point n := 3, f := g, from H2
  exact (Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint.positive_at_a_point (n := (3 : ℤ)) (by parley_side) (f := g) hH2)

end Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtThree

module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint

/-! Written from tests/elaborator/a-cited-letter-bound-in-its-own-hypothesis.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtThree

theorem positive_at_three (g : ℤ → ℝ) (hH2 : ∀ k : ℤ, 0 < k → g k > 0) :
    g 3 > 0 := by
  -- 1. thm:positive-at-a-point n := 3, f := g, from H2
  have s1 : g 3 > 0 := by first | linarith [(Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint.positive_at_a_point (n := (3 : ℤ)) (by parley_side) (f := g) (by parley_side))] | (have h := (Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint.positive_at_a_point (n := (3 : ℤ)) (by parley_side) (f := g) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint.positive_at_a_point (n := (3 : ℤ)) (by parley_side) (f := g) (by parley_side)) | (have h := (Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint.positive_at_a_point (n := (3 : ℤ)) (by parley_side) (f := g) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtThree

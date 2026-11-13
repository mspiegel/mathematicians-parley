module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-cited-letter-bound-in-its-own-hypothesis.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint

theorem positive_at_a_point (n : ℤ) (hH1 : 0 < n) (f : ℤ → ℝ) (hH3 : ∀ n : ℤ, 0 < n → f n > 0) :
    f n > 0 := by
  -- 1. instantiate n := n in H3
  exact (hH3 n hH1)

end Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint

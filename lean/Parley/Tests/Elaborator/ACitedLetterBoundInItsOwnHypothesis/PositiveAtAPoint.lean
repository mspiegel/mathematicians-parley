module

public import Parley.Library

/-! Written from tests/elaborator/a-cited-letter-bound-in-its-own-hypothesis.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint

theorem positive_at_a_point (n : ℕ) (hH1 : 0 < n) (f : ℤ → ℝ) (hH3 : ∀ n : ℕ, 0 < n → f (n : ℤ) > 0) :
    f (n : ℤ) > 0 := by
  -- 1. instantiate n := n in H3
  have s1 : f (n : ℤ) > 0 := by first | linarith [(hH3 n (by parley_side))] | (have h := (hH3 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (hH3 n (by parley_side))
  all_goals parley_side

end Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint

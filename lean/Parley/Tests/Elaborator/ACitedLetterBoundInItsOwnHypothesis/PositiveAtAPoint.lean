module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/a-cited-letter-bound-in-its-own-hypothesis.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint

theorem positive_at_a_point (n : ℤ) (hH1 : 0 < n) (f : ℤ → ℝ) (hH3 : ∀ n : ℤ, 0 < n → f n > 0) :
    f n > 0 := by
  -- 1. instantiate n := n in H3
  first | linarith [(hH3 n (by parley_side))] | (have h := (hH3 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (hH3 n (by parley_side)) | (have h := (hH3 n (by parley_side)); parley_side)

end Parley.Tests.Elaborator.ACitedLetterBoundInItsOwnHypothesis.PositiveAtAPoint

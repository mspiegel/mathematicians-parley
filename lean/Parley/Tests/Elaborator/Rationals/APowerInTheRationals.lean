module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/rationals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Rationals.APowerInTheRationals

theorem a_power_in_the_rationals (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 ≤ b) (c : ℤ) :
    True := by
  -- 1. membership
  exact trivial

end Parley.Tests.Elaborator.Rationals.APowerInTheRationals

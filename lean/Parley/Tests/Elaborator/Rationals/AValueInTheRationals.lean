module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/rationals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Rationals.AValueInTheRationals

theorem a_value_in_the_rationals (a : ℤ) (hH1 : 0 < a) (f : ℤ → ℤ) :
    True := by
  -- 1. membership, from H2
  exact trivial

end Parley.Tests.Elaborator.Rationals.AValueInTheRationals

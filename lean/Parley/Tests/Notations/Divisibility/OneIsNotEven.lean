module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Notation

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.OneIsNotEven

theorem one_is_not_even :
    ¬ Even (1 : ℤ) := by
  -- 1. arithmetic
  have s1 : ¬ Even (1 : ℤ) := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Divisibility.OneIsNotEven

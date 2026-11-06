module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination

/-! Written from tests/elaborator/primes-and-brackets.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PrimesAndBrackets.PrimeName

theorem prime_name (c : ℝ) (c' : ℝ) (hH3 : c' = c + 1) :
    c' - c = 1 := by
  -- 1. algebra, from H3
  have s1 : c' - c = 1 := by linear_combination (norm := parley_norm) hH3
  all_goals exact s1

end Parley.Tests.Elaborator.PrimesAndBrackets.PrimeName

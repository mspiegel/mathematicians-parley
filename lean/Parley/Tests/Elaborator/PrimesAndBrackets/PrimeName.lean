module

public import NormTactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/primes-and-brackets.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PrimesAndBrackets.PrimeName

theorem prime_name (c : ℝ) (c' : ℝ) (hH3 : c' = c + 1) :
    c' - c = 1 := by
  -- 1. algebra, from H3
  linear_combination (norm := parley_norm) hH3

end Parley.Tests.Elaborator.PrimesAndBrackets.PrimeName

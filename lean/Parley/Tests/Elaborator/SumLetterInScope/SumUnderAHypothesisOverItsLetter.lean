module

public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs

/-! Written from tests/elaborator/sum-letter-in-scope.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SumLetterInScope.SumUnderAHypothesisOverItsLetter

theorem sum_under_a_hypothesis_over_its_letter (n : ℤ) (hH1 : 0 < n) (x : ℝ) (hH3 : x > 0) (hH4 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) + x) : ℝ)) ≥ 0) :
    True := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. membership, from 1
  all_goals parley_side

end Parley.Tests.Elaborator.SumLetterInScope.SumUnderAHypothesisOverItsLetter

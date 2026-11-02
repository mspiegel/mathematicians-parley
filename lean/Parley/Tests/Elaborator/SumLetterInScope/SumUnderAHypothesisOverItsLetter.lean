module

public import LeanBridges

/-! Written from tests/elaborator/sum-letter-in-scope.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SumLetterInScope.SumUnderAHypothesisOverItsLetter

theorem sum_under_a_hypothesis_over_its_letter (n : ℕ) (hH1 : 0 < n) (x : ℝ) (hH3 : x > 0) (hH4 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), 1 / ((k : ℝ) + x)) ≥ 0) :
    True := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. membership, from 1
  all_goals parley_side

end Parley.Tests.Elaborator.SumLetterInScope.SumUnderAHypothesisOverItsLetter

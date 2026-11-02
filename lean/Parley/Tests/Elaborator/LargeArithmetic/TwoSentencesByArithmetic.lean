module

public import Tactics

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.TwoSentencesByArithmetic

theorem two_sentences_by_arithmetic :
    (2 + 2 : ℤ) = 4 ∧ (3 * 3 : ℤ) = 9 := by
  -- 1. arithmetic
  have s1a : (2 + 2 : ℤ) = 4 := by parley_arith
  have s1b : (3 * 3 : ℤ) = 9 := by parley_arith
  exact ⟨by parley_side, by parley_side⟩

end Parley.Tests.Elaborator.LargeArithmetic.TwoSentencesByArithmetic

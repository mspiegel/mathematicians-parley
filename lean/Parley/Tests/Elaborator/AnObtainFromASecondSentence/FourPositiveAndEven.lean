module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/an-obtain-from-a-second-sentence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnObtainFromASecondSentence.FourPositiveAndEven

theorem four_positive_and_even :
    (4 : ℤ) > 0 ∧ (∃ k : ℤ, 4 = 2 * k) := by
  -- 1. arithmetic
  have s1 : (4 : ℤ) = 2 * 2 := by parley_arith
  -- 2. exhibit, from 1
  have s2 : ∃ k : ℤ, 4 = 2 * k := ⟨(2 : ℤ), by parley_side⟩
  -- 3. arithmetic
  have s3 : (4 : ℤ) > 0 := by parley_arith
  -- 4. join 3, 2
  have s4a : (4 : ℤ) > 0 := by parley_side
  have s4b : ∃ k : ℤ, 4 = 2 * k := by parley_side
  exact ⟨by parley_side, by parley_side⟩

end Parley.Tests.Elaborator.AnObtainFromASecondSentence.FourPositiveAndEven

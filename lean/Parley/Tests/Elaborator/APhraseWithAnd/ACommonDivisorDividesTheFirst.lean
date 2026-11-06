module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Parley.Items.Tests.Elaborator.APhraseWithAnd

/-! Written from tests/elaborator/a-phrase-with-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseWithAnd.ACommonDivisorDividesTheFirst

theorem a_common_divisor_divides_the_first (a : ℤ) (b : ℤ) (d : ℤ) (hH4 : ((True ∧ d ∣ a) ∧ d ∣ b) ∧ d > 0) :
    d ∣ a := by
  -- 1. restate H4
  have s1 : (True ∧ d ∣ a) ∧ d ∣ b := by parley_side
  -- 2. D1, from 1
  have s2 : (True ∧ d ∣ a) ∧ d ∣ b := by parley_side
  -- 3. restate 2
  have s3 : d ∣ a := by parley_side
  all_goals exact s3

end Parley.Tests.Elaborator.APhraseWithAnd.ACommonDivisorDividesTheFirst

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Tests.Elaborator.AnObtainFromASecondSentence.FourPositiveAndEven

/-! Written from tests/elaborator/an-obtain-from-a-second-sentence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnObtainFromASecondSentence.AnObtainFromASecondSentence

theorem an_obtain_from_a_second_sentence :
    (∃ j : ℤ, 4 = 2 * j) := by
  -- 1. obtain j: thm:four-positive-and-even
  obtain ⟨j, s1⟩ := Parley.Tests.Elaborator.AnObtainFromASecondSentence.FourPositiveAndEven.four_positive_and_even.2
  -- 2. exhibit, from 1
  exact ⟨j, s1⟩

end Parley.Tests.Elaborator.AnObtainFromASecondSentence.AnObtainFromASecondSentence

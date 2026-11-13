module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
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
public import Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne

/-! Written from tests/elaborator/a-theorem-cited-at-other-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.CitedBesideALetterOfTheSameName

theorem cited_beside_a_letter_of_the_same_name (C : ℝ) (D : ℝ) :
    D + D - D = D := by
  -- 1. thm:a-double-less-one
  exact (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne.a_double_less_one (C := D))

end Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.CitedBesideALetterOfTheSameName

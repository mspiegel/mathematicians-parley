module

public import AlgebraTactics
public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/an-induction-whose-letter-a-hypothesis-binds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnInductionWhoseLetterAHypothesisBinds.AnInductionWhoseLetterAHypothesisBinds

theorem an_induction_whose_letter_a_hypothesis_binds (hH1 : ∀ m : ℕ, (m : ℤ) ≥ 0) :
    (∀ m : ℕ, (m : ℤ) + 0 = (m : ℤ)) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℕ, (m : ℤ) + 0 = (m : ℤ) := by
    intro m
    induction m with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (0 + 0 : ℤ) = 0 := by parley_arith
      all_goals parley_side
    | succ m hIH =>
      -- 1.2. algebra
      have s1_2 : (m : ℤ) + 1 + 0 = (m : ℤ) + 1 := by parley_ring
      all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.AnInductionWhoseLetterAHypothesisBinds.AnInductionWhoseLetterAHypothesisBinds

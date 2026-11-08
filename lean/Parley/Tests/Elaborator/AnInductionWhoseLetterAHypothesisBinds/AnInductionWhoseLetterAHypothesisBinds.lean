module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/an-induction-whose-letter-a-hypothesis-binds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnInductionWhoseLetterAHypothesisBinds.AnInductionWhoseLetterAHypothesisBinds

theorem an_induction_whose_letter_a_hypothesis_binds (hH1 : ∀ m : ℤ, 0 ≤ m → m ≥ 0) :
    (∀ m : ℤ, 0 ≤ m → m + 0 = m) := by
  -- 1. induction on m starting at 0
  intro m h_m
  replace h_m : 0 ≤ m := by omega
  induction m, h_m using LeanBridges.Functions.le_induction with
  | base =>
    -- 1.1. arithmetic
    parley_arith
  | succ m hK hIH =>
    -- 1.2. algebra
    parley_ring

end Parley.Tests.Elaborator.AnInductionWhoseLetterAHypothesisBinds.AnInductionWhoseLetterAHypothesisBinds

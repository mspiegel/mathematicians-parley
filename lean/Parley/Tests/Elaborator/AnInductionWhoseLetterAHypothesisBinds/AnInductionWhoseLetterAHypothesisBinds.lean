module

public import ArithTactics
public import Functions
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.RingNF

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
    ring_nf

end Parley.Tests.Elaborator.AnInductionWhoseLetterAHypothesisBinds.AnInductionWhoseLetterAHypothesisBinds

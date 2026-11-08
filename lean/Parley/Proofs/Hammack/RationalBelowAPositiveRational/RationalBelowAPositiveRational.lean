module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from proofs/hammack/rational-below-a-positive-rational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalBelowAPositiveRational.RationalBelowAPositiveRational

theorem rational_below_a_positive_rational (x : ℚ) (hH2 : x > 0) :
    (∃ y : ℚ, y > 0 ∧ y < x) := by
  -- 1. inequalities
  have s1 : x / 2 > 0 := by parley_order
  -- 2. inequalities
  have s2 : x / 2 < x := by parley_order
  -- 3. exhibit, from 1, 2
  exact ⟨x / 2, ⟨s1, s2⟩⟩

end Parley.Proofs.Hammack.RationalBelowAPositiveRational.RationalBelowAPositiveRational

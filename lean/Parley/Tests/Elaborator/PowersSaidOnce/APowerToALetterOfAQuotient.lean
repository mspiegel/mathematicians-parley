module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/powers-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PowersSaidOnce.APowerToALetterOfAQuotient

theorem a_power_to_a_letter_of_a_quotient (b : ℤ) (hH1 : 0 ≤ b) (x : ℝ) :
    x * ((b : ℝ) / 5) ^ b.toNat = ((b : ℝ) / 5) ^ b.toNat * x := by
  -- 1. algebra
  have s1 : x * ((b : ℝ) / 5) ^ b.toNat = ((b : ℝ) / 5) ^ b.toNat * x := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.PowersSaidOnce.APowerToALetterOfAQuotient

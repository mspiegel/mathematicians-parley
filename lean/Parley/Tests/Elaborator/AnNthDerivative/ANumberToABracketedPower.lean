module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/an-nth-derivative.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnNthDerivative.ANumberToABracketedPower

theorem a_number_to_a_bracketed_power (x : ℝ) (n : ℤ) (hH2 : 0 < n) :
    x ^ n.toNat = x ^ n.toNat := by
  -- 1. algebra
  have s1 : x ^ n.toNat = x ^ n.toNat := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.AnNthDerivative.ANumberToABracketedPower

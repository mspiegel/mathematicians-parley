module

public import AlgebraTactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/an-nth-derivative.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnNthDerivative.ANumberToABracketedPower

theorem a_number_to_a_bracketed_power (x : ℝ) (n : ℤ) (hH2 : 0 < n) :
    x ^ n.toNat = x ^ n.toNat := by
  -- 1. algebra
  parley_ring

end Parley.Tests.Elaborator.AnNthDerivative.ANumberToABracketedPower

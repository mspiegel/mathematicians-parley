module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
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

namespace Parley.Tests.Elaborator.PowersSaidOnce.APowerWhoseBaseHoldsAFactorial

theorem a_power_whose_base_holds_a_factorial (b : ℤ) (hH1 : 0 ≤ b) (x : ℝ) (z : ℂ) :
    (x : ℂ) * (z - (LeanBridges.Counting.factorial (4 : ℤ) : ℂ)) ^ b.toNat = (z - (LeanBridges.Counting.factorial (4 : ℤ) : ℂ)) ^ b.toNat * (x : ℂ) := by
  -- 1. algebra
  parley_ring

end Parley.Tests.Elaborator.PowersSaidOnce.APowerWhoseBaseHoldsAFactorial

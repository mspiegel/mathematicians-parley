module

public import Calculus
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/an-nth-derivative.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnNthDerivative.AnNthDerivativeDefined

theorem an_nth_derivative_defined (f : ℝ → ℝ) (n : ℤ) (hH2 : 0 < n) (c : ℝ) (hH4 : c ∈ LeanBridges.Calculus.derivDomain n.toNat f) :
    c ∈ LeanBridges.Calculus.derivDomain n.toNat f := by
  -- 1. restate H4
  exact hH4

end Parley.Tests.Elaborator.AnNthDerivative.AnNthDerivativeDefined

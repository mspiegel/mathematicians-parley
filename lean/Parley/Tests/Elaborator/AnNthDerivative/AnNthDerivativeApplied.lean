module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/an-nth-derivative.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnNthDerivative.AnNthDerivativeApplied

theorem an_nth_derivative_applied (f : ℝ → ℝ) (n : ℤ) (hH2 : 0 < n) (c : ℝ) (hH4 : (iteratedDeriv n.toNat f) c = 0) :
    (iteratedDeriv n.toNat f) c = 0 := by
  -- 1. restate H4
  exact hH4

end Parley.Tests.Elaborator.AnNthDerivative.AnNthDerivativeApplied

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainOfEquations

theorem a_chain_of_equations {α : Type*} [Nonempty α] (A : Set α) (B : Set α) (C : Set α) (hH4 : A = B) (hH5 : B = C) :
    A = C := by
  -- 1. transitivity, from H4, H5
  exact Eq.trans hH4 hH5

end Parley.Tests.Elaborator.Transitivity.AChainOfEquations

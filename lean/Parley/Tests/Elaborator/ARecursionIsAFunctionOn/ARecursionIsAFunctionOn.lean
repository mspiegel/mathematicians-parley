module

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
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-recursion-is-a-function-on.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARecursionIsAFunctionOn.ARecursionIsAFunctionOn

theorem a_recursion_is_a_function_on (F : ℤ → ℤ) (hD1 : F 0 = (1 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1)) :
    True := by
  -- 1. mun:function-into, from H1
  exact trivial

end Parley.Tests.Elaborator.ARecursionIsAFunctionOn.ARecursionIsAFunctionOn

module

public import Tactics
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-recursion-is-a-function-on.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARecursionIsAFunctionOn.ARecursionIsAFunctionOn

theorem a_recursion_is_a_function_on (F : ℤ → ℤ) (hD1 : F 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1) (hH1 : True) :
    True := by
  -- 1. mun:function-into, from H1
  all_goals parley_side

end Parley.Tests.Elaborator.ARecursionIsAFunctionOn.ARecursionIsAFunctionOn

module

public import Tactics
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-range-a-function-is-typed-over.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARangeAFunctionIsTypedOver.ARangeAFunctionIsTypedOver

theorem a_range_a_function_is_typed_over (n : ℤ) (hH1 : 0 < n) (a : ℤ → ℝ) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) n) :
    True := by
  -- 1. mun:function-value f := a, from H3
  all_goals parley_side

end Parley.Tests.Elaborator.ARangeAFunctionIsTypedOver.ARangeAFunctionIsTypedOver

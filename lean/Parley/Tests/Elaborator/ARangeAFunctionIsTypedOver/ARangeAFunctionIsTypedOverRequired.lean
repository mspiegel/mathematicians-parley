module

public import LeanBridges
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-range-a-function-is-typed-over.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARangeAFunctionIsTypedOver.ARangeAFunctionIsTypedOverRequired

theorem a_range_a_function_is_typed_over_required (n : ℕ) (hH1 : 0 < n) (a : ℤ → ℝ) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    a k + 0 = a k := by
  -- 1. algebra
  have s1 : a k + 0 = a k := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.ARangeAFunctionIsTypedOver.ARangeAFunctionIsTypedOverRequired

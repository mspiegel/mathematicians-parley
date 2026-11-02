module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-named-value-of-a-function.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANamedValueOfAFunction.ANamedValueOfAFunction

theorem a_named_value_of_a_function (n : ℕ) (hH1 : 0 < n) (a : ℤ → ℝ) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    a k ^ 2 ≥ 0 := by
  set x : ℝ := a k with hD1
  -- 1. mun:square-nonneg
  have s1 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
  -- 2. calculation
  have s2 : a k ^ 2 ≥ 0 := by
    calc a k ^ 2 = x ^ 2 := by parley_side
      _ ≥ 0 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ANamedValueOfAFunction.ANamedValueOfAFunction

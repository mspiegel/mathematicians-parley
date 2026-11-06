module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-named-value-of-a-function.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANamedValueOfAFunction.ANamedValueOfAFunction

theorem a_named_value_of_a_function (n : ℤ) (hH1 : 0 < n) (a : ℤ → ℝ) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) n) :
    a k ^ 2 ≥ 0 := by
  set x : ℝ := a k with hD1
  have hD1_kind : True := by parley_side
  -- 1. mun:square-nonneg
  have s1 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_side)
  -- 2. calculation
  have s2 : a k ^ 2 ≥ 0 := by
    calc a k ^ 2 = x ^ 2 := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      _ ≥ 0 := by parley_side
  all_goals exact s2

end Parley.Tests.Elaborator.ANamedValueOfAFunction.ANamedValueOfAFunction

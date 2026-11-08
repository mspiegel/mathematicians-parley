module

public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnProduct

theorem ln_product (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) :
    Real.log (x * y) = Real.log x + Real.log y := by
  -- 1. mun:logarithms-ln-product, from H3, H4
  exact (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) hH3 hH4)

end Parley.Tests.Stdlib.Logarithms.LnProduct

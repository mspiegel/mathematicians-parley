module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnProduct

theorem ln_product (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) :
    Real.log (x * y) = Real.log x + Real.log y := by
  -- 1. mun:logarithms-ln-product, from H3, H4
  exact (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) hH3 hH4)

end Parley.Tests.Stdlib.Logarithms.LnProduct

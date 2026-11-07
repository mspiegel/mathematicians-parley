module

public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnOrder

theorem ln_order (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) :
    (x < y ↔ Real.log x < Real.log y) := by
  -- 1. mun:logarithms-ln-order, from H3, H4
  have s1 : x < y ↔ Real.log x < Real.log y := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_order (x := x) (y := y) (by parley_side) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Logarithms.LnOrder

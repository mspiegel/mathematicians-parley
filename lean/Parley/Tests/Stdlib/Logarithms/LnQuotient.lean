module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnQuotient

theorem ln_quotient (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) :
    Real.log (x / y) = Real.log x - Real.log y := by
  -- 1. mun:logarithms-ln-quotient, from H3, H4
  have s1 : Real.log (x / y) = Real.log x - Real.log y := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := x) (y := y) (by parley_side) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Logarithms.LnQuotient

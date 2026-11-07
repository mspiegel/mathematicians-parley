module

public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnExp

theorem ln_exp (x : ℝ) :
    Real.log (Real.exp x) = x := by
  -- 1. mun:logarithms-ln-exp
  have s1 : Real.log (Real.exp x) = x := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := x))
  all_goals exact s1

end Parley.Tests.Stdlib.Logarithms.LnExp

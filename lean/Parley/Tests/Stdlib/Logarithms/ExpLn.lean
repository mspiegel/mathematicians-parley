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

namespace Parley.Tests.Stdlib.Logarithms.ExpLn

theorem exp_ln (x : ℝ) (hH2 : x > 0) :
    Real.exp (Real.log x) = x := by
  -- 1. mun:logarithms-exp-ln, from H2
  have s1 : Real.exp (Real.log x) = x := by exact (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Logarithms.ExpLn

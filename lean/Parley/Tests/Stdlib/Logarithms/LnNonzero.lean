module

public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnNonzero

theorem ln_nonzero (x : ℝ) (hH2 : x > 0) (hH3 : x ≠ 1) :
    Real.log x ≠ 0 := by
  -- 1. mun:logarithms-ln-nonzero, from H2, H3
  exact (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) hH2 hH3)

end Parley.Tests.Stdlib.Logarithms.LnNonzero

module

public import SubstTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/hammack/ln-is-injective.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LnIsInjective.LnIsInjective

theorem ln_is_injective (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) (hH5 : Real.log x = Real.log y) :
    x = y := by
  -- 1. calculation
  calc x = Real.exp (Real.log x) := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) hH3).symm
    _ = Real.exp (Real.log y) := by parley_subst hH5
    _ = y := by exact (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := y) hH4)

end Parley.Proofs.Hammack.LnIsInjective.LnIsInjective

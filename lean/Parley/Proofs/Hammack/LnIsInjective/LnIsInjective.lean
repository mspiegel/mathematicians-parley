module

public import Mathlib.Analysis.Complex.Exponential
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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/hammack/ln-is-injective.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LnIsInjective.LnIsInjective

theorem ln_is_injective (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) (hH5 : Real.log x = Real.log y) :
    x = y := by
  -- 1. calculation
  calc x = Real.exp (Real.log x) := by exact (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) hH3).symm
    _ = Real.exp (Real.log y) := by (have h := congrArg (fun t : ℝ => Real.exp t) hH5; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = y := by exact (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := y) hH4)

end Parley.Proofs.Hammack.LnIsInjective.LnIsInjective

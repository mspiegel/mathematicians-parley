module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedInATransitivityChain

theorem a_define_applied_in_a_transitivity_chain (a : ℤ) (hH1 : 0 < a) (x : ℝ) (y : ℝ) (q : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → q j = j + 1) (hH4 : x < (q a : ℝ)) (hH5 : (a : ℝ) + 1 < y) :
    x < y := by
  -- 1. transitivity, from H4, D1, H5
  exact lt_trans (LT.lt.trans_eq hH4 (show (q a : ℝ) = (a : ℝ) + 1 by exact_mod_cast hD1 _ hH1)) hH5

end Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedInATransitivityChain

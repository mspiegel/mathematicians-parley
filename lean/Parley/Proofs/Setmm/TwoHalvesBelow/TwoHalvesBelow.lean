module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from proofs/setmm/two-halves-below.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.TwoHalvesBelow.TwoHalvesBelow

theorem two_halves_below (A : ℝ) (B : ℝ) (C : ℝ) (hH4 : A < C / 2) (hH5 : B < C / 2) :
    A + B < C := by
  -- 1. inequalities, from H4, H5
  parley_order

end Parley.Proofs.Setmm.TwoHalvesBelow.TwoHalvesBelow

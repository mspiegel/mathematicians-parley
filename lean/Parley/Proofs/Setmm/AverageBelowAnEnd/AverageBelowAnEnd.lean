module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from proofs/setmm/average-below-an-end.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AverageBelowAnEnd.AverageBelowAnEnd

theorem average_below_an_end (A : ℝ) (B : ℝ) :
    (A < B ↔ (A + B) / 2 < B) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. inequalities
    parley_order
  · skip
    intro hD2
    -- 2. inequalities
    parley_order

end Parley.Proofs.Setmm.AverageBelowAnEnd.AverageBelowAnEnd

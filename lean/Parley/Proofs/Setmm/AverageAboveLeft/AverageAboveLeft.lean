module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from proofs/setmm/average-above-left.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AverageAboveLeft.AverageAboveLeft

theorem average_above_left (A : ℝ) (B : ℝ) :
    (A < B ↔ A < (A + B) / 2) := by
  -- the theorem. both directions
  have sThm : A < B ↔ A < (A + B) / 2 := by
    constructor
    · skip
      intro hD1
      -- 1. inequalities
      have s1 : A < (A + B) / 2 := by parley_order
      all_goals parley_side
    · skip
      intro hD2
      -- 2. inequalities
      have s2 : A < B := by parley_order
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.AverageAboveLeft.AverageAboveLeft

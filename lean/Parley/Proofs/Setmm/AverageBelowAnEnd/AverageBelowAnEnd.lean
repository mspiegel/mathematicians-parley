module

public import OrderTactics
public import Tactics

/-! Written from proofs/setmm/average-below-an-end.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AverageBelowAnEnd.AverageBelowAnEnd

theorem average_below_an_end (A : ℝ) (B : ℝ) :
    (A < B ↔ (A + B) / 2 < B) := by
  -- the theorem. both directions
  have sThm : A < B ↔ (A + B) / 2 < B := by
    constructor
    · skip
      intro hD1
      -- 1. inequalities
      have s1 : (A + B) / 2 < B := by parley_order
      all_goals parley_side
    · skip
      intro hD2
      -- 2. inequalities
      have s2 : A < B := by parley_order
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.AverageBelowAnEnd.AverageBelowAnEnd

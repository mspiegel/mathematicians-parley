module

public import Parley.Library

/-! Written from proofs/setmm/average-below-an-end.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AverageBelowAnEnd.AverageBelowAnEnd

theorem average_below_an_end (A : ℝ) (B : ℝ) :
    (A < B ↔ (A + B) / 2 < B) := by
  -- the theorem. both directions
  have sThm : A < B ↔ (A + B) / 2 < B := by
    constructor
    · skip
      intro D1
      -- 1. inequalities
      have s1 : (A + B) / 2 < B := by parley_side
      parley_side
    · skip
      intro D2
      -- 2. inequalities
      have s2 : A < B := by parley_side
      parley_side
  parley_side

end Parley.Proofs.Setmm.AverageBelowAnEnd.AverageBelowAnEnd

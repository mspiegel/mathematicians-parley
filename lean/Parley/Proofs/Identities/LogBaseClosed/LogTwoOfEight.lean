module

public import RealTactics
public import Tactics

/-! Written from proofs/identities/log-base-closed.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseClosed.LogTwoOfEight

theorem log_two_of_eight :
    Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 := by
  -- 1. substitute ln(8) = 3·ln(2) (real arithmetic)
  have s1 : Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) / Real.log (2 : ℝ) := by parley_subst (show Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) by parley_real)
  -- 2. calculation
  have r11_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  have s2 : Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 := by
    calc Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) / Real.log (2 : ℝ) := by parley_side
      _ = 3 := by parley_ring
  all_goals exact s2

end Parley.Proofs.Identities.LogBaseClosed.LogTwoOfEight

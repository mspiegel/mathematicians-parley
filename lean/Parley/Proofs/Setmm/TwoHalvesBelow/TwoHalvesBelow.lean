module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic

/-! Written from proofs/setmm/two-halves-below.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.TwoHalvesBelow.TwoHalvesBelow

theorem two_halves_below (A : ℝ) (B : ℝ) (C : ℝ) (hH4 : A < C / 2) (hH5 : B < C / 2) :
    A + B < C := by
  -- 1. inequalities, from H4, H5
  have s1 : A + B < C := by parley_order
  all_goals exact s1

end Parley.Proofs.Setmm.TwoHalvesBelow.TwoHalvesBelow

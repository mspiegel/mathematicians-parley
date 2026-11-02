module

public import LeanBridges

/-! Written from proofs/setmm/two-halves-below.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.TwoHalvesBelow.TwoHalvesBelow

theorem two_halves_below (A : ℝ) (B : ℝ) (C : ℝ) (hH4 : A < C / 2) (hH5 : B < C / 2) :
    A + B < C := by
  -- 1. inequalities, from H4, H5
  have s1 : A + B < C := by parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.TwoHalvesBelow.TwoHalvesBelow

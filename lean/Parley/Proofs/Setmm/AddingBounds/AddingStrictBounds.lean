module

public import Tactics

/-! Written from proofs/setmm/adding-bounds.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AddingBounds.AddingStrictBounds

theorem adding_strict_bounds (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ) (hH5 : A < C) (hH6 : B < D) :
    A + B < C + D := by
  -- 1. inequalities, from H5, H6
  have s1 : A + B < C + D := by parley_order
  all_goals parley_side

end Parley.Proofs.Setmm.AddingBounds.AddingStrictBounds

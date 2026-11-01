module

public import Parley.Library

/-! Written from proofs/setmm/adding-bounds.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AddingBounds.AddingBounds

theorem adding_bounds (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ) (H5 : A ≤ C) (H6 : B ≤ D) :
    A + B ≤ C + D := by
  -- 1. inequalities, from H5, H6
  have s1 : A + B ≤ C + D := by linarith
  parley_side

end Parley.Proofs.Setmm.AddingBounds.AddingBounds

module

public import LeanBridges
public import Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds

/-! Written from proofs/setmm/difference-not-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceNotZero.DifferenceNotZero

theorem difference_not_zero (A : ℝ) (B : ℝ) (hH3 : abs A < B) :
    B - A ≠ 0 := by
  -- 1. thm:abs-bounds x := A
  have s1a : A ≤ abs A := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).1] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).1 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).1; parley_side)
  have s1b : -A ≤ abs A := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).2] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).2; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).2 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).2; parley_side)
  -- 2. inequalities, from 1
  have s2 : A ≤ abs A := by parley_side
  -- 3. transitivity, from 2, H3
  have s3 : A < B := by parley_side
  -- 4. inequalities
  have s4 : B - A ≠ 0 := by parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.DifferenceNotZero.DifferenceNotZero

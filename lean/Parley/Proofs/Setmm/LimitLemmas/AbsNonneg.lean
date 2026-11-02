module

public import Tactics
public import Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds

/-! Written from proofs/setmm/limit-lemmas.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitLemmas.AbsNonneg

theorem abs_nonneg (x : ℝ) :
    abs x ≥ 0 := by
  -- 1. thm:abs-bounds
  have s1a : x ≤ abs x := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).1] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).1 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).1; parley_side)
  have s1b : -x ≤ abs x := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).2] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).2; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).2 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).2; parley_side)
  -- 2. inequalities, from 1
  have s2 : 0 ≤ 2 * abs x := by parley_order
  -- 3. inequalities
  have s3 : abs x ≥ 0 := by parley_order
  all_goals parley_side

end Parley.Proofs.Setmm.LimitLemmas.AbsNonneg

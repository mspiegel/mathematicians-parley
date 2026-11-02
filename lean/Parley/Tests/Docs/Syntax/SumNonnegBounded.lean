module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library
public import Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds

/-! Written from tests/docs/syntax.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Syntax.SumNonnegBounded

theorem sum_nonneg_bounded (a : ℝ) (b : ℝ) (hH3 : a + b ≥ 0) :
    abs (a + b) ≤ abs a + abs b := by
  -- 1. thm:abs-bounds x := a
  have s1a : a ≤ abs a := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).1] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).1
  have s1b : -a ≤ abs a := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).2] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).2; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).2
  -- 2. thm:abs-bounds x := b
  have s2a : b ≤ abs b := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).1] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).1
  have s2b : -b ≤ abs b := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).2] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).2; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).2
  -- 3. def:abs x := a + b, from H3
  have s3 : abs (a + b) = a + b := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side); qify; linear_combination (norm := parley_norm) h)
  -- 4. inequalities, from 1, 2
  have s4 : a + b ≤ abs a + abs b := by parley_side
  -- 5. calculation
  have s5 : abs (a + b) ≤ abs a + abs b := by
    calc abs (a + b) = a + b := by parley_side
      _ ≤ abs a + abs b := by parley_side
  all_goals parley_side

end Parley.Tests.Docs.Syntax.SumNonnegBounded

module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds

/-! Written from proofs/wiedijk/triangle-inequality.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.TriangleInequality.TriangleInequality

theorem triangle_inequality (a : ℝ) (b : ℝ) :
    abs (a + b) ≤ abs a + abs b := by
  -- 1. mun:nonneg-or-neg x := a + b
  have s1 : a + b ≥ 0 ∨ a + b < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b))
  -- 2. thm:abs-bounds x := a
  have s2a : a ≤ abs a := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).1
  have s2b : -a ≤ abs a := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).2
  -- 3. thm:abs-bounds x := b
  have s3a : b ≤ abs b := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).1
  have s3b : -b ≤ abs b := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).2
  -- 4. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 4.1. inequalities, from 2, 3
    have s4_1 : a + b ≤ abs a + abs b := by linarith only [s2a, s3a]
    -- 4.2. calculation
    calc abs (a + b) = a + b := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) hC1
      _ ≤ abs a + abs b := s4_1
  · skip
    -- 4.3. inequalities, from 2, 3
    have s4_3 : -a + -b ≤ abs a + abs b := by linarith only [s2b, s3b]
    -- 4.4. calculation
    calc abs (a + b) = -(a + b) := by exact (Parley.Items.Stdlib.Numbers.def_abs_2 (x := a + b)) hC2
      _ = -a + -b := by parley_ring
      _ ≤ abs a + abs b := s4_3

end Parley.Proofs.Wiedijk.TriangleInequality.TriangleInequality

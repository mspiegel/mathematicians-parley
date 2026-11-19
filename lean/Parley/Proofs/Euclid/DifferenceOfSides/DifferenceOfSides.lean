module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry

/-! Written from proofs/euclid/difference-of-sides.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.DifferenceOfSides.DifferenceOfSides

theorem difference_of_sides (A : ℂ) (B : ℂ) (C : ℂ) :
    dist A B - dist A C ≤ dist B C ∧ dist A C - dist A B ≤ dist B C := by
  -- 1. thm:triangle-inequality-points P := A, Q := C, R := B
  have s1 : dist A B ≤ dist A C + dist C B := by exact (Parley.Items.Stdlib.Geometry.thm_triangle_inequality_points (P := A) (Q := C) (R := B))
  -- 2. inequalities
  have s2 : dist A B - dist A C ≤ dist B C := by
    rw [dist_comm C B] at s1
    exact (by linarith only [s1])
  -- 3. thm:triangle-inequality-points P := A, Q := B, R := C
  have s3 : dist A C ≤ dist A B + dist B C := by exact (Parley.Items.Stdlib.Geometry.thm_triangle_inequality_points (P := A) (Q := B) (R := C))
  -- 4. inequalities
  have s4 : dist A C - dist A B ≤ dist B C := by linarith only [s3]
  -- 5. join 2, 4
  have s5a : dist A B - dist A C ≤ dist B C := s2
  have s5b : dist A C - dist A B ≤ dist B C := s4
  exact ⟨s5a, s5b⟩

end Parley.Proofs.Euclid.DifferenceOfSides.DifferenceOfSides

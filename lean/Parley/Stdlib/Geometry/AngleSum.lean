module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.AlternateAngles
public import Parley.Stdlib.Geometry.AnglesOnALine
public import Parley.Stdlib.Geometry.ParallelThrough

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.AngleSum

theorem angle_sum (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) :
    EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A = (180 : ℝ) * Real.pi / 180 := by
  -- 1. obtain D, E: thm:parallel-through P := A, Q := C, R := B, from H4
  obtain ⟨D, s1a, E, s1b, ⟨⟨⟨⟨⟨s1c, s1d⟩, s1e⟩, s1f⟩, s1g⟩, s1h⟩⟩ := (Parley.Stdlib.Geometry.ParallelThrough.parallel_through (P := A) (Q := C) (R := B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B))
  -- 2. thm:alternate-angles P := A, Q := C, R := B, S := D, from H4, 1
  have s2 : EuclideanGeometry.angle D B A = EuclideanGeometry.angle B A C := by exact (Parley.Stdlib.Geometry.AlternateAngles.alternate_angles (P := A) (Q := C) (R := B) (S := D) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) s1c s1f)
  -- 3. thm:alternate-angles P := C, Q := A, R := B, S := E, from H4, 1
  have s3 : EuclideanGeometry.angle E B C = EuclideanGeometry.angle B C A := by exact (Parley.Stdlib.Geometry.AlternateAngles.alternate_angles (P := C) (Q := A) (R := B) (S := E) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_312 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C A B) s1d s1g)
  -- 4. calculation
  have r2304_1 : B ≠ C := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_1 (A := B) (B := C) (P := E) (Q := A) s1g)
  have r2304_2 : ¬ E ∈ LeanBridges.Geometry.line B C := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_2 (A := B) (B := C) (P := E) (Q := A) s1g)
  have r2304_3 : LeanBridges.Geometry.Triangle C B E := (by (have h := (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := E) (Q := B) (R := C) r2304_1 r2304_2); rw [LeanBridges.Geometry.triangle_swap_13 E B C] at h; exact h) : LeanBridges.Geometry.Triangle C B E)
  calc EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A = EuclideanGeometry.angle D B A + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A := congrArg (fun t : ℝ => t + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A) s2.symm
    _ = EuclideanGeometry.angle D B A + EuclideanGeometry.angle A B C + EuclideanGeometry.angle E B C := congrArg (fun t : ℝ => EuclideanGeometry.angle D B A + EuclideanGeometry.angle A B C + t) s3.symm
    _ = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Stdlib.Geometry.AnglesOnALine.angles_on_a_line (P := A) (Q := C) (R := B) (S := D) (T := E) s1e s1h s1f r2304_3)

end Parley.Stdlib.Geometry.AngleSum

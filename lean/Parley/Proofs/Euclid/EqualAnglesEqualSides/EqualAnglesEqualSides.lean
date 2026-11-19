module

public import Geometry
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.AngleSideAngle

/-! Written from proofs/euclid/equal-angles-equal-sides.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.EqualAnglesEqualSides.EqualAnglesEqualSides

theorem equal_angles_equal_sides (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : EuclideanGeometry.angle C A B = EuclideanGeometry.angle C B A) :
    dist C A = dist C B := by
  -- 1. calculation
  have s1 : EuclideanGeometry.angle A B C = EuclideanGeometry.angle B A C := by
    calc EuclideanGeometry.angle A B C = EuclideanGeometry.angle C B A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := A) (Q := B) (R := C) hH4)
      _ = EuclideanGeometry.angle C A B := hH5.symm
      _ = EuclideanGeometry.angle B A C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := C) (Q := A) (R := B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_312 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C A B))
  -- 2. thm:angle-side-angle D := B, E := A, F := C, from H4, H5, 1
  have s2 : dist A B = dist B A ∧ dist B C = dist A C ∧ dist C A = dist C B ∧ EuclideanGeometry.angle A B C = EuclideanGeometry.angle B A C ∧ EuclideanGeometry.angle B C A = EuclideanGeometry.angle A C B ∧ EuclideanGeometry.angle C A B = EuclideanGeometry.angle C B A := by exact (Parley.Stdlib.Geometry.AngleSideAngle.angle_side_angle (A := A) (B := B) (C := C) (D := B) (E := A) (F := C) hH4 (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C) hH5 (by rw [dist_comm A B]) s1)
  -- 3. def:congruent, from H4, 2
  exact (by (have h := (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := B) (Q := B) (Q' := A) (R := C) (R' := C) hH4 (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C))).mp s2).1.1.1.1.2.symm; rw [dist_comm B C, dist_comm A C] at h; exact h) : dist C A = dist C B)

end Parley.Proofs.Euclid.EqualAnglesEqualSides.EqualAnglesEqualSides

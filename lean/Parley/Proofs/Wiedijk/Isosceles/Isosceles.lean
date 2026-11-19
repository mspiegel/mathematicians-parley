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

/-! Written from proofs/wiedijk/isosceles.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Isosceles.Isosceles

theorem isosceles (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : dist C A = dist C B) :
    EuclideanGeometry.angle C A B = EuclideanGeometry.angle C B A := by
  -- 1. mun:angle-symmetric P := A, Q := C, R := B, from H4
  have s1 : EuclideanGeometry.angle A C B = EuclideanGeometry.angle B C A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := A) (Q := C) (R := B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B))
  -- 2. axi:side-angle-side P := A, Q := C, R := B, P′ := B, Q′ := C, R′ := A, from H4, H5, 1
  have s2 : dist A C = dist B C ∧ dist C B = dist C A ∧ dist B A = dist A B ∧ EuclideanGeometry.angle A C B = EuclideanGeometry.angle B C A ∧ EuclideanGeometry.angle C B A = EuclideanGeometry.angle C A B ∧ EuclideanGeometry.angle B A C = EuclideanGeometry.angle A B C := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := A) (P' := B) (Q := C) (Q' := C) (R := B) (R' := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A) (by (have h := hH5; rw [dist_comm C A, dist_comm C B] at h; exact h) : dist A C = dist B C) s1 hH5.symm)
  -- 3. calculation
  calc EuclideanGeometry.angle C A B = EuclideanGeometry.angle B A C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := C) (Q := A) (R := B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_312 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C A B))
    _ = EuclideanGeometry.angle A B C := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := B) (Q := C) (Q' := C) (R := B) (R' := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A))).mp s2).2
    _ = EuclideanGeometry.angle C B A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := A) (Q := B) (R := C) hH4)

end Parley.Proofs.Wiedijk.Isosceles.Isosceles

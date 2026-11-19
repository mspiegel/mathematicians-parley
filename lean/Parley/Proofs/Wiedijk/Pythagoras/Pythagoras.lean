module

public import Geometry
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Proofs.Wiedijk.Pythagoras.SimilarTriangles
public import Parley.Stdlib.Geometry.AltitudeFoot

/-! Written from proofs/wiedijk/pythagoras.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Pythagoras.Pythagoras

theorem pythagoras (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180) :
    dist A B ^ 2 = dist A C ^ 2 + dist B C ^ 2 := by
  -- 1. obtain D: thm:altitude-foot P := A, Q := B, R := C, from H4, H5
  obtain ⟨D, s1a, ⟨⟨⟨⟨s1b, s1c⟩, s1d⟩, s1e⟩, s1f⟩⟩ := (Parley.Stdlib.Geometry.AltitudeFoot.altitude_foot (P := A) (Q := B) (R := C) hH4 hH5)
  -- 2. calculation
  have s2 : EuclideanGeometry.angle D A C = EuclideanGeometry.angle C A B := by
    calc EuclideanGeometry.angle D A C = EuclideanGeometry.angle B A C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := A) (Q := B) (R := C) (S := D) s1b (Ne.symm s1c.2.2.1) (Ne.symm s1c.2.1) (Ne.symm s1d.2.2.1))
      _ = EuclideanGeometry.angle C A B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := B) (Q := A) (R := C) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C))
  -- 3. calculation
  have s3 : EuclideanGeometry.angle A D C = EuclideanGeometry.angle A C B := by
    calc EuclideanGeometry.angle A D C = (90 : ℝ) * Real.pi / 180 := s1e
      _ = EuclideanGeometry.angle A C B := hH5.symm
  -- 4. thm:similar-triangles P := A, Q := D, R := C, P′ := A, Q′ := C, R′ := B, from H4, 1, 2, 3
  have s4 : dist A D * dist A B = dist A C * dist A C := by exact (Parley.Proofs.Wiedijk.Pythagoras.SimilarTriangles.similar_triangles (P := A) (Q := D) (R := C) (P' := A) (Q' := C) (R' := B) s1c (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) s2 s3)
  -- 5. calculation
  have s5 : EuclideanGeometry.angle D B C = EuclideanGeometry.angle C B A := by
    calc EuclideanGeometry.angle D B C = EuclideanGeometry.angle A B C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := B) (Q := A) (R := C) (S := D) (by (have h := s1b; rw [sbtw_comm (x := A) (y := D) (z := B)] at h; exact h) : Sbtw ℝ B D A) (Ne.symm s1d.2.2.1) (Ne.symm s1c.2.1) (Ne.symm s1c.2.2.1))
      _ = EuclideanGeometry.angle C B A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := A) (Q := B) (R := C) hH4)
  -- 6. calculation
  have s6 : EuclideanGeometry.angle B D C = EuclideanGeometry.angle B C A := by
    calc EuclideanGeometry.angle B D C = (90 : ℝ) * Real.pi / 180 := s1f
      _ = EuclideanGeometry.angle A C B := hH5.symm
      _ = EuclideanGeometry.angle B C A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := B) (Q := C) (R := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A)).symm
  -- 7. thm:similar-triangles P := B, Q := D, R := C, P′ := B, Q′ := C, R′ := A, from H4, 1, 5, 6
  have s7 : dist B D * dist B A = dist B C * dist B C := by exact (Parley.Proofs.Wiedijk.Pythagoras.SimilarTriangles.similar_triangles (P := B) (Q := D) (R := C) (P' := B) (Q' := C) (R' := A) s1d (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A) s5 s6)
  -- 8. mun:segment-addition P := A, Q := B, S := D, from 1
  have s8 : dist A D + dist D B = dist A B := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := B) (S := D) s1b)
  -- 9. algebra, from 4, 7, 8
  rw [dist_comm B A] at s7
  rw [dist_comm D B] at s8
  exact (by linear_combination s4 + s7 + (-dist A B) * s8)

end Parley.Proofs.Wiedijk.Pythagoras.Pythagoras

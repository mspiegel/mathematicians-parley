module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
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
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Proofs.Wiedijk.Pythagoras.Pythagoras

/-! Written from proofs/euclid/altitude-mean-proportional.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.AltitudeMeanProportional.AltitudeMeanProportional

theorem altitude_mean_proportional (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (hH5 : LeanBridges.Geometry.Triangle A B C) (hH6 : EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180) (hH7 : Sbtw ℝ A D B) (hH8 : C ≠ D) (hH9 : EuclideanGeometry.angle A D C = (90 : ℝ) * Real.pi / 180) :
    dist C D ^ 2 = dist A D * dist D B := by
  -- 1. mun:between-apart R := D, S := A, T := B, from H7
  have s1a : A ≠ D := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := D) (S := A) (T := B) hH7)
  have s1b : B ≠ D := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := D) (S := A) (T := B) hH7)
  -- 2. thm:pythagoras, from H5, H6
  have s2 : dist A B ^ 2 = dist A C ^ 2 + dist B C ^ 2 := by exact (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := A) (B := B) (C := C) hH5 hH6)
  -- 3. mun:right-angle-triangle P := A, Q := D, R := C, from H5, H8, H9, 1
  have s3 : LeanBridges.Geometry.Triangle A D C := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := A) (Q := D) (R := C) s1a hH8 hH9 hH5.2.2.1)
  -- 4. thm:pythagoras B := C, C := D, from H9, 3
  have s4 : dist A C ^ 2 = dist A D ^ 2 + dist C D ^ 2 := by exact (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := A) (B := C) (C := D) (by (have h := s3; rw [LeanBridges.Geometry.triangle_swap_23 A D C] at h; exact h) : LeanBridges.Geometry.Triangle A C D) hH9)
  -- 5. axi:supplementary-angles B := D, C := B, D := C, from H5, H7, H8
  have s5 : EuclideanGeometry.angle A D C + EuclideanGeometry.angle C D B = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := A) (B := D) (C := B) (D := C) hH7 hH8 (Ne.symm hH5.2.2.1) (Ne.symm hH5.2.1))
  -- 6. algebra, from H9, 5
  have s6 : EuclideanGeometry.angle C D B = (90 : ℝ) * Real.pi / 180 := by linear_combination ((-32400) / ((180) * (180))) * hH9 + ((32400) / ((180) * (180))) * s5
  -- 7. mun:right-angle-triangle P := C, Q := D, R := B, from H5, H8, 1, 6
  have s7 : LeanBridges.Geometry.Triangle C D B := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := C) (Q := D) (R := B) hH8 s1b s6 (Ne.symm hH5.2.1))
  -- 8. thm:pythagoras A := C, C := D, from 6, 7
  have s8 : dist C B ^ 2 = dist C D ^ 2 + dist B D ^ 2 := by exact (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := C) (B := B) (C := D) (by (have h := s7; rw [LeanBridges.Geometry.triangle_swap_23 C D B] at h; exact h) : LeanBridges.Geometry.Triangle C B D) s6)
  -- 9. mun:segment-addition P := A, Q := B, S := D, from H7
  have s9 : dist A D + dist D B = dist A B := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := B) (S := D) hH7)
  -- 10. calculation
  have s10 : 2 * dist C D ^ 2 = 2 * (dist A D * dist D B) := by
    calc 2 * dist C D ^ 2 = dist A C ^ 2 + dist B C ^ 2 - dist A D ^ 2 - dist D B ^ 2 := by
          rw [dist_comm C B] at s8
          rw [dist_comm D B]
          exact (by linear_combination (-1) * s4 + (-1) * s8)
      _ = dist A B ^ 2 - dist A D ^ 2 - dist D B ^ 2 := congrArg (fun t : ℝ => t - dist A D ^ 2 - dist D B ^ 2) s2.symm
      _ = (dist A D + dist D B) ^ 2 - dist A D ^ 2 - dist D B ^ 2 := congrArg (fun t : ℝ => t ^ 2 - dist A D ^ 2 - dist D B ^ 2) s9.symm
      _ = 2 * (dist A D * dist D B) := by ring1
  -- 11. algebra, from 10
  linear_combination ((1 / 2 : ℝ)) * s10

end Parley.Proofs.Euclid.AltitudeMeanProportional.AltitudeMeanProportional

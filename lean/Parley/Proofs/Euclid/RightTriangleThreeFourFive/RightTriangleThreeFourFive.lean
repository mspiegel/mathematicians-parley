module

public import Geometry
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Euclid.ConverseOfPythagoras.ConverseOfPythagoras

/-! Written from proofs/euclid/right-triangle-three-four-five.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.RightTriangleThreeFourFive.RightTriangleThreeFourFive

theorem right_triangle_three_four_five (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : A = Complex.mk (0 : ℝ) (0 : ℝ)) (hH5 : B = Complex.mk (3 : ℝ) (0 : ℝ)) (hH6 : C = Complex.mk (0 : ℝ) (4 : ℝ)) :
    LeanBridges.Geometry.Triangle A B C ∧ EuclideanGeometry.angle B A C = (90 : ℝ) * Real.pi / 180 ∧ dist B C = 5 := by
  -- 1. arithmetic
  have s1 : (((0 : ℤ), (0 : ℤ)) : ℤ × ℤ) ≠ ((3 : ℤ), (0 : ℤ)) := fun h => (show (0 : ℤ) ≠ 3 by norm_num) (congrArg Prod.fst h)
  -- 2. mun:points-apart-by-coordinates, from H4, H5, 1
  have s2 : A ≠ B := ((Parley.Items.Stdlib.Geometry.mun_points_apart_by_coordinates (A := A) (B := B) (a := (0 : ℝ)) (b := (0 : ℝ)) (c := (3 : ℝ)) (d := (0 : ℝ)) hH4 hH5)).mpr (by (have h := s1; revert h; norm_num))
  -- 3. arithmetic
  have s3 : (((0 : ℤ), (0 : ℤ)) : ℤ × ℤ) ≠ ((0 : ℤ), (4 : ℤ)) := fun h => (show (0 : ℤ) ≠ 4 by norm_num) (congrArg Prod.snd h)
  -- 4. mun:points-apart-by-coordinates, from H4, H6, 3
  have s4 : A ≠ C := ((Parley.Items.Stdlib.Geometry.mun_points_apart_by_coordinates (A := A) (B := C) (a := (0 : ℝ)) (b := (0 : ℝ)) (c := (0 : ℝ)) (d := (4 : ℝ)) hH4 hH6)).mpr (by (have h := s3; revert h; norm_num))
  -- 5. arithmetic
  have s5 : (((3 : ℤ), (0 : ℤ)) : ℤ × ℤ) ≠ ((0 : ℤ), (4 : ℤ)) := fun h => (show (3 : ℤ) ≠ 0 by norm_num) (congrArg Prod.fst h)
  -- 6. mun:points-apart-by-coordinates, from H5, H6, 5
  have s6 : B ≠ C := ((Parley.Items.Stdlib.Geometry.mun_points_apart_by_coordinates (A := B) (B := C) (a := (3 : ℝ)) (b := (0 : ℝ)) (c := (0 : ℝ)) (d := (4 : ℝ)) hH5 hH6)).mpr (by (have h := s5; revert h; norm_num))
  -- 7. mun:collinear-by-coordinates
  have s7 : Collinear ℝ {Complex.mk (0 : ℝ) (0 : ℝ), Complex.mk (3 : ℝ) (0 : ℝ), Complex.mk (0 : ℝ) (4 : ℝ)} ↔ ((3 - 0) * (4 - 0) : ℤ) = (0 - 0) * (0 - 0) := by
    have hI : Collinear ℝ {Complex.mk (0 : ℝ) (0 : ℝ), Complex.mk (3 : ℝ) (0 : ℝ), Complex.mk (0 : ℝ) (4 : ℝ)} ↔ ((3 - 0) * (4 - 0) : ℤ) = (0 - 0) * (0 - 0) := by exact_mod_cast ((Parley.Items.Stdlib.Geometry.mun_collinear_by_coordinates (a := (0 : ℝ)) (b := (0 : ℝ)) (c := (3 : ℝ)) (d := (0 : ℝ)) (e := (0 : ℝ)) (f := (4 : ℝ))))
    exact hI
  -- 8. substitute
  have s8 : Collinear ℝ {A, B, C} ↔ ((3 - 0) * (4 - 0) : ℤ) = (0 - 0) * (0 - 0) := by
    have c1 : Complex.mk (0 : ℝ) (0 : ℝ) = A := congrArg (fun t : ℂ => t) hH4.symm
    have row1 : Collinear ℝ {A, Complex.mk (3 : ℝ) (0 : ℝ), Complex.mk (0 : ℝ) (4 : ℝ)} ↔ ((3 - 0) * (4 - 0) : ℤ) = (0 - 0) * (0 - 0) := Eq.subst (motive := (fun t : ℂ => Collinear ℝ {t, Complex.mk (3 : ℝ) (0 : ℝ), Complex.mk (0 : ℝ) (4 : ℝ)} ↔ ((3 - 0) * (4 - 0) : ℤ) = (0 - 0) * (0 - 0))) c1 s7
    have c2 : Complex.mk (3 : ℝ) (0 : ℝ) = B := congrArg (fun t : ℂ => t) hH5.symm
    have row2 : Collinear ℝ {A, B, Complex.mk (0 : ℝ) (4 : ℝ)} ↔ ((3 - 0) * (4 - 0) : ℤ) = (0 - 0) * (0 - 0) := Eq.subst (motive := (fun t : ℂ => Collinear ℝ {A, t, Complex.mk (0 : ℝ) (4 : ℝ)} ↔ ((3 - 0) * (4 - 0) : ℤ) = (0 - 0) * (0 - 0))) c2 row1
    have c3 : Complex.mk (0 : ℝ) (4 : ℝ) = C := congrArg (fun t : ℂ => t) hH6.symm
    have row3 : Collinear ℝ {A, B, C} ↔ ((3 - 0) * (4 - 0) : ℤ) = (0 - 0) * (0 - 0) := Eq.subst (motive := (fun t : ℂ => Collinear ℝ {A, B, t} ↔ ((3 - 0) * (4 - 0) : ℤ) = (0 - 0) * (0 - 0))) c3 row2
    exact row3
  -- 9. arithmetic
  have s9 : ((3 - 0) * (4 - 0) : ℤ) ≠ (0 - 0) * (0 - 0) := by norm_num
  -- 10. mun:iff-not-from-right, from 8, 9
  have s10 : ¬ Collinear ℝ {A, B, C} := by exact (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := Collinear ℝ {A, B, C}) (Q := ((3 - 0) * (4 - 0) : ℤ) = (0 - 0) * (0 - 0)) s8 s9)
  -- 11. def:triangle, from 2, 4, 6, 10
  have s11 : LeanBridges.Geometry.Triangle A B C := ((Parley.Items.Stdlib.Geometry.def_triangle (P := A) (Q := B) (R := C))).mpr ⟨⟨⟨s2, s6⟩, s4⟩, s10⟩
  -- 12. calculation
  have s12 : dist B A = 3 := by
    calc dist B A = Real.sqrt ((3 - 0) ^ 2 + (0 - 0) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := B) (B := A) (a := (3 : ℝ)) (b := (0 : ℝ)) (c := (0 : ℝ)) (d := (0 : ℝ)) hH5 hH4)
      _ = Real.sqrt (9 : ℝ) := by norm_num
      _ = 3 := by
          have hv1 : Real.sqrt (9 : ℝ) = 3 := by rw [congrArg Real.sqrt (show (9 : ℝ) = 3 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 3 by norm_num)]
          linear_combination hv1
  -- 13. calculation
  have s13 : dist A C = 4 := by
    calc dist A C = Real.sqrt ((0 - 0) ^ 2 + (0 - 4) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := A) (B := C) (a := (0 : ℝ)) (b := (0 : ℝ)) (c := (0 : ℝ)) (d := (4 : ℝ)) hH4 hH6)
      _ = Real.sqrt (16 : ℝ) := by norm_num
      _ = 4 := by
          have hv1 : Real.sqrt (16 : ℝ) = 4 := by rw [congrArg Real.sqrt (show (16 : ℝ) = 4 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 4 by norm_num)]
          linear_combination hv1
  -- 14. calculation
  have s14 : dist B C = 5 := by
    calc dist B C = Real.sqrt ((3 - 0) ^ 2 + (0 - 4) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := B) (B := C) (a := (3 : ℝ)) (b := (0 : ℝ)) (c := (0 : ℝ)) (d := (4 : ℝ)) hH5 hH6)
      _ = Real.sqrt (25 : ℝ) := by norm_num
      _ = 5 := by
          have hv1 : Real.sqrt (25 : ℝ) = 5 := by rw [congrArg Real.sqrt (show (25 : ℝ) = 5 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 5 by norm_num)]
          linear_combination hv1
  -- 15. calculation
  have s15 : dist B C ^ 2 = dist B A ^ 2 + dist C A ^ 2 := by
    calc dist B C ^ 2 = 5 ^ 2 := congrArg (fun t : ℝ => t ^ 2) s14
      _ = 3 ^ 2 + 4 ^ 2 := by norm_num
      _ = dist B A ^ 2 + 4 ^ 2 := congrArg (fun t : ℝ => t ^ 2 + 4 ^ 2) s12.symm
      _ = dist B A ^ 2 + dist C A ^ 2 := by (have h := (by (have h := congrArg (fun t : ℝ => dist B A ^ 2 + t ^ 2) s13.symm; rw [dist_comm A C] at h; exact h) : dist B A ^ 2 + 4 ^ 2 = dist B A ^ 2 + dist C A ^ 2); push_cast at h ⊢; exact_mod_cast h)
  -- 16. thm:converse-of-pythagoras A := B, B := C, C := A, from 11, 15
  have s16 : EuclideanGeometry.angle B A C = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Proofs.Euclid.ConverseOfPythagoras.ConverseOfPythagoras.converse_of_pythagoras (A := B) (B := C) (C := A) (by (have h := s11; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A) s15)
  -- 17. join 11, 16, 14
  have s17a : LeanBridges.Geometry.Triangle A B C := s11
  have s17b : EuclideanGeometry.angle B A C = (90 : ℝ) * Real.pi / 180 := s16
  have s17c : dist B C = 5 := s14
  exact ⟨s17a, s17b, s17c⟩

end Parley.Proofs.Euclid.RightTriangleThreeFourFive.RightTriangleThreeFourFive

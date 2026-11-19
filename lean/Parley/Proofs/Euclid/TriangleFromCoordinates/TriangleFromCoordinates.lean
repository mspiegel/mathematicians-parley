module

public import Geometry
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/euclid/triangle-from-coordinates.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.TriangleFromCoordinates.TriangleFromCoordinates

theorem triangle_from_coordinates (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : A = Complex.mk (4 : ℝ) (1 : ℝ)) (hH5 : B = Complex.mk (-2 : ℝ) (-3 : ℝ)) (hH6 : C = Complex.mk (5 : ℝ) (0 : ℝ)) :
    LeanBridges.Geometry.Triangle A B C := by
  -- 1. arithmetic
  have s1 : (((4 : ℤ), (1 : ℤ)) : ℤ × ℤ) ≠ ((-2 : ℤ), (-3 : ℤ)) := fun h => (show (4 : ℤ) ≠ -2 by norm_num) (congrArg Prod.fst h)
  -- 2. mun:points-apart-by-coordinates, from H4, H5, 1
  have s2 : A ≠ B := ((Parley.Items.Stdlib.Geometry.mun_points_apart_by_coordinates (A := A) (B := B) (a := (4 : ℝ)) (b := (1 : ℝ)) (c := (-2 : ℝ)) (d := (-3 : ℝ)) hH4 hH5)).mpr (by (have h := s1; revert h; norm_num))
  -- 3. arithmetic
  have s3 : (((-2 : ℤ), (-3 : ℤ)) : ℤ × ℤ) ≠ ((5 : ℤ), (0 : ℤ)) := fun h => (show (-2 : ℤ) ≠ 5 by norm_num) (congrArg Prod.fst h)
  -- 4. mun:points-apart-by-coordinates, from H5, H6, 3
  have s4 : B ≠ C := ((Parley.Items.Stdlib.Geometry.mun_points_apart_by_coordinates (A := B) (B := C) (a := (-2 : ℝ)) (b := (-3 : ℝ)) (c := (5 : ℝ)) (d := (0 : ℝ)) hH5 hH6)).mpr (by (have h := s3; revert h; norm_num))
  -- 5. arithmetic
  have s5 : (((4 : ℤ), (1 : ℤ)) : ℤ × ℤ) ≠ ((5 : ℤ), (0 : ℤ)) := fun h => (show (4 : ℤ) ≠ 5 by norm_num) (congrArg Prod.fst h)
  -- 6. mun:points-apart-by-coordinates, from H4, H6, 5
  have s6 : A ≠ C := ((Parley.Items.Stdlib.Geometry.mun_points_apart_by_coordinates (A := A) (B := C) (a := (4 : ℝ)) (b := (1 : ℝ)) (c := (5 : ℝ)) (d := (0 : ℝ)) hH4 hH6)).mpr (by (have h := s5; revert h; norm_num))
  -- 7. mun:collinear-by-coordinates
  have s7 : Collinear ℝ {Complex.mk (4 : ℝ) (1 : ℝ), Complex.mk (-2 : ℝ) (-3 : ℝ), Complex.mk (5 : ℝ) (0 : ℝ)} ↔ ((-2 - 4) * (0 - 1) : ℤ) = (5 - 4) * (-3 - 1) := by
    have hI : Collinear ℝ {Complex.mk (4 : ℝ) (1 : ℝ), Complex.mk (-2 : ℝ) (-3 : ℝ), Complex.mk (5 : ℝ) (0 : ℝ)} ↔ ((-2 - 4) * (0 - 1) : ℤ) = (5 - 4) * (-3 - 1) := by exact_mod_cast ((Parley.Items.Stdlib.Geometry.mun_collinear_by_coordinates (a := (4 : ℝ)) (b := (1 : ℝ)) (c := (-2 : ℝ)) (d := (-3 : ℝ)) (e := (5 : ℝ)) (f := (0 : ℝ))))
    exact hI
  -- 8. substitute
  have s8 : Collinear ℝ {A, B, C} ↔ ((-2 - 4) * (0 - 1) : ℤ) = (5 - 4) * (-3 - 1) := by
    have c1 : Complex.mk (4 : ℝ) (1 : ℝ) = A := congrArg (fun t : ℂ => t) hH4.symm
    have row1 : Collinear ℝ {A, Complex.mk (-2 : ℝ) (-3 : ℝ), Complex.mk (5 : ℝ) (0 : ℝ)} ↔ ((-2 - 4) * (0 - 1) : ℤ) = (5 - 4) * (-3 - 1) := Eq.subst (motive := (fun t : ℂ => Collinear ℝ {t, Complex.mk (-2 : ℝ) (-3 : ℝ), Complex.mk (5 : ℝ) (0 : ℝ)} ↔ ((-2 - 4) * (0 - 1) : ℤ) = (5 - 4) * (-3 - 1))) c1 s7
    have c2 : Complex.mk (-2 : ℝ) (-3 : ℝ) = B := congrArg (fun t : ℂ => t) hH5.symm
    have row2 : Collinear ℝ {A, B, Complex.mk (5 : ℝ) (0 : ℝ)} ↔ ((-2 - 4) * (0 - 1) : ℤ) = (5 - 4) * (-3 - 1) := Eq.subst (motive := (fun t : ℂ => Collinear ℝ {A, t, Complex.mk (5 : ℝ) (0 : ℝ)} ↔ ((-2 - 4) * (0 - 1) : ℤ) = (5 - 4) * (-3 - 1))) c2 row1
    have c3 : Complex.mk (5 : ℝ) (0 : ℝ) = C := congrArg (fun t : ℂ => t) hH6.symm
    have row3 : Collinear ℝ {A, B, C} ↔ ((-2 - 4) * (0 - 1) : ℤ) = (5 - 4) * (-3 - 1) := Eq.subst (motive := (fun t : ℂ => Collinear ℝ {A, B, t} ↔ ((-2 - 4) * (0 - 1) : ℤ) = (5 - 4) * (-3 - 1))) c3 row2
    exact row3
  -- 9. arithmetic
  have s9 : ((-2 - 4) * (0 - 1) : ℤ) ≠ (5 - 4) * (-3 - 1) := by norm_num
  -- 10. mun:iff-not-from-right, from 8, 9
  have s10 : ¬ Collinear ℝ {A, B, C} := by exact (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := Collinear ℝ {A, B, C}) (Q := ((-2 - 4) * (0 - 1) : ℤ) = (5 - 4) * (-3 - 1)) s8 s9)
  -- 11. def:triangle, from 2, 4, 6, 10
  exact ((Parley.Items.Stdlib.Geometry.def_triangle (P := A) (Q := B) (R := C))).mpr ⟨⟨⟨s2, s4⟩, s6⟩, s10⟩

end Parley.Proofs.Euclid.TriangleFromCoordinates.TriangleFromCoordinates

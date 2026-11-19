module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Convex.Between
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
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from proofs/euclid/three-points-on-a-line.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.ThreePointsOnALine.ThreePointsOnALine

theorem three_points_on_a_line (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : A = Complex.mk (1 : ℝ) (1 : ℝ)) (hH5 : B = Complex.mk (2 : ℝ) (3 : ℝ)) (hH6 : C = Complex.mk (4 : ℝ) (7 : ℝ)) :
    Collinear ℝ {A, B, C} ∧ Sbtw ℝ A B C := by
  -- 1. arithmetic
  have s1 : ((1 - 2) * (7 - 3) : ℤ) = (4 - 2) * (1 - 3) := by norm_num
  -- 2. arithmetic
  have s2 : ((1 - 2) * (4 - 2) + (1 - 3) * (7 - 3) : ℤ) < 0 := by norm_num
  -- 3. mun:between-by-coordinates, from 1, 2
  have s3 : Sbtw ℝ (Complex.mk (1 : ℝ) (1 : ℝ)) (Complex.mk (2 : ℝ) (3 : ℝ)) (Complex.mk (4 : ℝ) (7 : ℝ)) := ((Parley.Items.Stdlib.Geometry.mun_between_by_coordinates (a := (1 : ℝ)) (b := (1 : ℝ)) (c := (2 : ℝ)) (d := (3 : ℝ)) (e := (4 : ℝ)) (f := (7 : ℝ)))).mpr ⟨by norm_num, by norm_num⟩
  -- 4. substitute
  have s4 : Sbtw ℝ A B C := by
    have c1 : Complex.mk (2 : ℝ) (3 : ℝ) = B := congrArg (fun t : ℂ => t) hH5.symm
    have row1 : Sbtw ℝ (Complex.mk (1 : ℝ) (1 : ℝ)) B (Complex.mk (4 : ℝ) (7 : ℝ)) := Eq.subst (motive := (fun t : ℂ => Sbtw ℝ (Complex.mk (1 : ℝ) (1 : ℝ)) t (Complex.mk (4 : ℝ) (7 : ℝ)))) c1 s3
    have c2 : Complex.mk (1 : ℝ) (1 : ℝ) = A := congrArg (fun t : ℂ => t) hH4.symm
    have row2 : Sbtw ℝ A B (Complex.mk (4 : ℝ) (7 : ℝ)) := Eq.subst (motive := (fun t : ℂ => Sbtw ℝ t B (Complex.mk (4 : ℝ) (7 : ℝ)))) c2 row1
    have c3 : Complex.mk (4 : ℝ) (7 : ℝ) = C := congrArg (fun t : ℂ => t) hH6.symm
    have row3 : Sbtw ℝ A B C := Eq.subst (motive := (fun t : ℂ => Sbtw ℝ A B t)) c3 row2
    exact row3
  -- 5. mun:between-collinear, from 4
  have s5 : Collinear ℝ {A, B, C} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := B) (S := C) (T := A) (by (have h := s4; rw [sbtw_comm (x := A) (y := B) (z := C)] at h; exact h) : Sbtw ℝ C B A))
  -- 6. join 5, 4
  have s6a : Collinear ℝ {A, B, C} := s5
  have s6b : Sbtw ℝ A B C := s4
  exact ⟨s6a, s6b⟩

end Parley.Proofs.Euclid.ThreePointsOnALine.ThreePointsOnALine

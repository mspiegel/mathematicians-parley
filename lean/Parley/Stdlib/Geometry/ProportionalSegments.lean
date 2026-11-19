module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers
public import Parley.Stdlib.Geometry.AreaTurned
public import Parley.Stdlib.Geometry.Foot
public import Parley.Stdlib.Geometry.HeightArea
public import Parley.Stdlib.Geometry.SameBaseArea
public import Parley.Stdlib.Geometry.SameHeight

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.ProportionalSegments

theorem proportional_segments (P : ℂ) (Q : ℂ) (R : ℂ) (X : ℂ) (Y : ℂ) (hH6 : LeanBridges.Geometry.Triangle P Q R) (hH7 : Sbtw ℝ P X Q) (hH8 : Sbtw ℝ P Y R) (hH9 : Complex.im ((Y - X) / (R - Q)) = 0) :
    dist P X * dist P R = dist P Y * dist P Q := by
  -- 1. mun:triangle-on-side P := Q, Q := P, S := Y, from H6, H8
  have s1 : LeanBridges.Geometry.Triangle Q P Y := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := Q) (Q := P) (R := R) (S := Y) (by (have h := hH6; rw [LeanBridges.Geometry.triangle_swap_12 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle Q P R) hH8)
  -- 2. mun:triangle-on-side P := R, Q := P, R := Q, S := X, from H6, H7
  have s2 : LeanBridges.Geometry.Triangle R P X := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := R) (Q := P) (R := Q) (S := X) (by (have h := hH6; rw [LeanBridges.Geometry.triangle_rot_312 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R P Q) hH7)
  -- 3. axi:area-addition P := Y, Q := P, R := Q, D := X, from H7, 1
  have s3 : 1 / 2 * (dist P Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (P - Q)))) = 1 / 2 * (dist P X * dist Y X) * abs (Real.sin (Complex.arg ((Y - X) / (P - X)))) + 1 / 2 * (dist X Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (X - Q)))) := by exact (Parley.Items.Stdlib.Geometry.axi_area_addition (D := X) (P := Y) (Q := P) (R := Q) (by (have h := s1; rw [LeanBridges.Geometry.triangle_swap_13 Q P Y] at h; exact h) : LeanBridges.Geometry.Triangle Y P Q) hH7)
  -- 4. mun:triangle-on-side P := Y, R := P, S := X, from H7, 1
  have s4 : LeanBridges.Geometry.Triangle Y Q X := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := Y) (Q := Q) (R := P) (S := X) (by (have h := s1; rw [LeanBridges.Geometry.triangle_rot_312 Q P Y] at h; exact h) : LeanBridges.Geometry.Triangle Y Q P) (by (have h := hH7; rw [sbtw_comm (x := P) (y := X) (z := Q)] at h; exact h) : Sbtw ℝ Q X P))
  -- 5. mun:triangle-on-side P := X, Q := R, R := P, S := Y, from H8, 2
  have s5 : LeanBridges.Geometry.Triangle X R Y := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := X) (Q := R) (R := P) (S := Y) (by (have h := s2; rw [LeanBridges.Geometry.triangle_rot_312 R P X] at h; exact h) : LeanBridges.Geometry.Triangle X R P) (by (have h := hH8; rw [sbtw_comm (x := P) (y := Y) (z := R)] at h; exact h) : Sbtw ℝ R Y P))
  -- 6. mun:triangle-on-side P := Y, Q := P, R := Q, S := X, from H7, 1
  have s6 : LeanBridges.Geometry.Triangle Y P X := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := Y) (Q := P) (R := Q) (S := X) (by (have h := s1; rw [LeanBridges.Geometry.triangle_swap_13 Q P Y] at h; exact h) : LeanBridges.Geometry.Triangle Y P Q) hH7)
  -- 7. calculation
  have s7 : 1 / 2 * (dist X Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (X - Q)))) = 1 / 2 * (dist Y R * dist X R) * abs (Real.sin (Complex.arg ((X - R) / (Y - R)))) := by
    calc 1 / 2 * (dist X Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (X - Q)))) = 1 / 2 * (dist Q Y * dist X Y) * abs (Real.sin (Complex.arg ((X - Y) / (Q - Y)))) := by exact (Parley.Items.Stdlib.Geometry.mun_area_rotated (P := Y) (Q := X) (R := Q) (by (have h := s4; rw [LeanBridges.Geometry.triangle_swap_23 Y Q X] at h; exact h) : LeanBridges.Geometry.Triangle Y X Q))
      _ = 1 / 2 * (dist Y X * dist Q X) * abs (Real.sin (Complex.arg ((Q - X) / (Y - X)))) := by exact (Parley.Items.Stdlib.Geometry.mun_area_rotated (P := X) (Q := Q) (R := Y) (by (have h := s4; rw [LeanBridges.Geometry.triangle_swap_13 Y Q X] at h; exact h) : LeanBridges.Geometry.Triangle X Q Y))
      _ = 1 / 2 * (dist X Y * dist Q Y) * abs (Real.sin (Complex.arg ((Q - Y) / (X - Y)))) := by exact (Parley.Stdlib.Geometry.AreaTurned.area_turned (P := Q) (Q := Y) (R := X) (by (have h := s4; rw [LeanBridges.Geometry.triangle_swap_12 Y Q X] at h; exact h) : LeanBridges.Geometry.Triangle Q Y X))
      _ = 1 / 2 * (dist X Y * dist R Y) * abs (Real.sin (Complex.arg ((R - Y) / (X - Y)))) := by exact (Parley.Stdlib.Geometry.SameBaseArea.same_base_area (Q := Q) (R := R) (X := X) (Y := Y) hH6.2.1 (by (have h := s4; rw [LeanBridges.Geometry.triangle_rot_231 Y Q X] at h; exact h) : LeanBridges.Geometry.Triangle Q X Y) (by (have h := s5; rw [LeanBridges.Geometry.triangle_swap_12 X R Y] at h; exact h) : LeanBridges.Geometry.Triangle R X Y) hH9)
      _ = 1 / 2 * (dist R X * dist Y X) * abs (Real.sin (Complex.arg ((Y - X) / (R - X)))) := by exact (Parley.Items.Stdlib.Geometry.mun_area_rotated (P := Y) (Q := R) (R := X) (by (have h := s5; rw [LeanBridges.Geometry.triangle_swap_13 X R Y] at h; exact h) : LeanBridges.Geometry.Triangle Y R X)).symm
      _ = 1 / 2 * (dist Y R * dist X R) * abs (Real.sin (Complex.arg ((X - R) / (Y - R)))) := by exact (Parley.Items.Stdlib.Geometry.mun_area_rotated (P := X) (Q := Y) (R := R) (by (have h := s5; rw [LeanBridges.Geometry.triangle_swap_23 X R Y] at h; exact h) : LeanBridges.Geometry.Triangle X Y R)).symm
  -- 8. calculation
  have s8 : 1 / 2 * (dist P X * dist Y X) * abs (Real.sin (Complex.arg ((Y - X) / (P - X)))) = 1 / 2 * (dist P Y * dist X Y) * abs (Real.sin (Complex.arg ((X - Y) / (P - Y)))) := by
    calc 1 / 2 * (dist P X * dist Y X) * abs (Real.sin (Complex.arg ((Y - X) / (P - X)))) = 1 / 2 * (dist X Y * dist P Y) * abs (Real.sin (Complex.arg ((P - Y) / (X - Y)))) := by exact (Parley.Items.Stdlib.Geometry.mun_area_rotated (P := Y) (Q := P) (R := X) s6)
      _ = 1 / 2 * (dist Y P * dist X P) * abs (Real.sin (Complex.arg ((X - P) / (Y - P)))) := by exact (Parley.Items.Stdlib.Geometry.mun_area_rotated (P := P) (Q := X) (R := Y) (by (have h := s6; rw [LeanBridges.Geometry.triangle_rot_231 Y P X] at h; exact h) : LeanBridges.Geometry.Triangle P X Y))
      _ = 1 / 2 * (dist P Y * dist X Y) * abs (Real.sin (Complex.arg ((X - Y) / (P - Y)))) := by exact (Parley.Stdlib.Geometry.AreaTurned.area_turned (P := X) (Q := Y) (R := P) (by (have h := s6; rw [LeanBridges.Geometry.triangle_rot_312 Y P X] at h; exact h) : LeanBridges.Geometry.Triangle X Y P))
  -- 9. substitute
  have s9 : 1 / 2 * (dist P Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (P - Q)))) = 1 / 2 * (dist P Y * dist X Y) * abs (Real.sin (Complex.arg ((X - Y) / (P - Y)))) + 1 / 2 * (dist Y R * dist X R) * abs (Real.sin (Complex.arg ((X - R) / (Y - R)))) := by
    have c1 : 1 / 2 * (dist P X * dist Y X) * abs (Real.sin (Complex.arg ((Y - X) / (P - X)))) = 1 / 2 * (dist P Y * dist X Y) * abs (Real.sin (Complex.arg ((X - Y) / (P - Y)))) := congrArg (fun t : ℝ => t) s8
    have row1 : 1 / 2 * (dist P Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (P - Q)))) = 1 / 2 * (dist P Y * dist X Y) * abs (Real.sin (Complex.arg ((X - Y) / (P - Y)))) + 1 / 2 * (dist X Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (X - Q)))) := Eq.subst (motive := (fun t : ℝ => 1 / 2 * (dist P Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (P - Q)))) = t + 1 / 2 * (dist X Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (X - Q)))))) c1 s3
    have c2 : 1 / 2 * (dist X Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (X - Q)))) = 1 / 2 * (dist Y R * dist X R) * abs (Real.sin (Complex.arg ((X - R) / (Y - R)))) := congrArg (fun t : ℝ => t) s7
    have row2 : 1 / 2 * (dist P Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (P - Q)))) = 1 / 2 * (dist P Y * dist X Y) * abs (Real.sin (Complex.arg ((X - Y) / (P - Y)))) + 1 / 2 * (dist Y R * dist X R) * abs (Real.sin (Complex.arg ((X - R) / (Y - R)))) := Eq.subst (motive := (fun t : ℝ => 1 / 2 * (dist P Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (P - Q)))) = 1 / 2 * (dist P Y * dist X Y) * abs (Real.sin (Complex.arg ((X - Y) / (P - Y)))) + t)) c2 row1
    exact row2
  -- 10. calculation
  have s10 : 1 / 2 * (dist P Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (P - Q)))) = 1 / 2 * (dist P R * dist X R) * abs (Real.sin (Complex.arg ((X - R) / (P - R)))) := by
    calc 1 / 2 * (dist P Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (P - Q)))) = 1 / 2 * (dist P Y * dist X Y) * abs (Real.sin (Complex.arg ((X - Y) / (P - Y)))) + 1 / 2 * (dist Y R * dist X R) * abs (Real.sin (Complex.arg ((X - R) / (Y - R)))) := s9
      _ = 1 / 2 * (dist P R * dist X R) * abs (Real.sin (Complex.arg ((X - R) / (P - R)))) := by exact (Parley.Items.Stdlib.Geometry.axi_area_addition (D := Y) (P := X) (Q := P) (R := R) (by (have h := s2; rw [LeanBridges.Geometry.triangle_swap_13 R P X] at h; exact h) : LeanBridges.Geometry.Triangle X P R) hH8).symm
  -- 11. obtain M, U: mun:foot P := Y, Q := P, R := Q, from 1
  obtain ⟨M, s11a, U, s11b, ⟨⟨⟨⟨⟨s11c, s11d⟩, s11e⟩, s11f⟩, s11g⟩, s11h⟩⟩ := (Parley.Stdlib.Geometry.Foot.foot (P := Y) (Q := P) (R := Q) (by (have h := s1; rw [LeanBridges.Geometry.triangle_swap_13 Q P Y] at h; exact h) : LeanBridges.Geometry.Triangle Y P Q))
  -- 12. obtain N, V: mun:foot P := X, Q := P, from 2
  obtain ⟨N, s12a, V, s12b, ⟨⟨⟨⟨⟨s12c, s12d⟩, s12e⟩, s12f⟩, s12g⟩, s12h⟩⟩ := (Parley.Stdlib.Geometry.Foot.foot (P := X) (Q := P) (R := R) (by (have h := s2; rw [LeanBridges.Geometry.triangle_swap_13 R P X] at h; exact h) : LeanBridges.Geometry.Triangle X P R))
  -- 13. mun:between-collinear R := X, S := P, T := Q, from H7
  have s13 : Collinear ℝ {Q, X, P} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := X) (S := P) (T := Q) hH7)
  -- 14. def:on-line P := X, A := P, B := Q, from H6, 13
  have s14 : X ∈ LeanBridges.Geometry.line P Q := ((Parley.Items.Stdlib.Geometry.def_on_line (A := P) (B := Q) (P := X) hH6.1)).mpr (by (have h := s13; rw [LeanBridges.Geometry.collinear_rot_312 Q X P] at h; exact h) : Collinear ℝ {P, Q, X})
  -- 15. mun:between-apart R := X, S := P, T := Q, from H7
  have s15a : P ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := X) (S := P) (T := Q) hH7)
  have s15b : Q ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := X) (S := P) (T := Q) hH7)
  -- 16. thm:same-height P := Y, Q := P, R := Q, S := X, H := M, T := U, from 1, 11, 14, 15
  have s16 : 1 / 2 * (dist P X * dist Y X) * abs (Real.sin (Complex.arg ((Y - X) / (P - X)))) = 1 / 2 * dist P X * dist Y M := by exact (Parley.Stdlib.Geometry.SameHeight.same_height (P := Y) (Q := P) (R := Q) (S := X) (H := M) (T := U) (by (have h := s1; rw [LeanBridges.Geometry.triangle_swap_13 Q P Y] at h; exact h) : LeanBridges.Geometry.Triangle Y P Q) s14 (Ne.symm s15a) s11c s11d s11e s11f s11g s11h)
  -- 17. mun:between-collinear R := Y, S := P, T := R, from H8
  have s17 : Collinear ℝ {R, Y, P} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := Y) (S := P) (T := R) hH8)
  -- 18. def:on-line P := Y, A := P, B := R, from H6, 17
  have s18 : Y ∈ LeanBridges.Geometry.line P R := ((Parley.Items.Stdlib.Geometry.def_on_line (A := P) (B := R) (P := Y) hH6.2.2.1)).mpr (by (have h := s17; rw [LeanBridges.Geometry.collinear_rot_312 R Y P] at h; exact h) : Collinear ℝ {P, R, Y})
  -- 19. mun:between-apart R := Y, S := P, T := R, from H8
  have s19a : P ≠ Y := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := Y) (S := P) (T := R) hH8)
  have s19b : R ≠ Y := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := Y) (S := P) (T := R) hH8)
  -- 20. thm:same-height P := X, Q := P, S := Y, H := N, T := V, from 2, 12, 18, 19
  have s20 : 1 / 2 * (dist P Y * dist X Y) * abs (Real.sin (Complex.arg ((X - Y) / (P - Y)))) = 1 / 2 * dist P Y * dist X N := by exact (Parley.Stdlib.Geometry.SameHeight.same_height (P := X) (Q := P) (R := R) (S := Y) (H := N) (T := V) (by (have h := s2; rw [LeanBridges.Geometry.triangle_swap_13 R P X] at h; exact h) : LeanBridges.Geometry.Triangle X P R) s18 (Ne.symm s19a) s12c s12d s12e s12f s12g s12h)
  -- 21. calculation
  have s21 : 1 / 2 * dist P Q * dist Y M = 1 / 2 * dist P R * dist X N := by
    calc 1 / 2 * dist P Q * dist Y M = 1 / 2 * (dist P Q * dist Y Q) * abs (Real.sin (Complex.arg ((Y - Q) / (P - Q)))) := by exact (Parley.Stdlib.Geometry.HeightArea.height_area (P := Y) (Q := P) (R := Q) (H := M) (S := U) (by (have h := s1; rw [LeanBridges.Geometry.triangle_swap_13 Q P Y] at h; exact h) : LeanBridges.Geometry.Triangle Y P Q) s11c s11d s11e s11f s11g s11h).symm
      _ = 1 / 2 * (dist P R * dist X R) * abs (Real.sin (Complex.arg ((X - R) / (P - R)))) := s10
      _ = 1 / 2 * dist P R * dist X N := by exact (Parley.Stdlib.Geometry.HeightArea.height_area (P := X) (Q := P) (R := R) (H := N) (S := V) (by (have h := s2; rw [LeanBridges.Geometry.triangle_swap_13 R P X] at h; exact h) : LeanBridges.Geometry.Triangle X P R) s12c s12d s12e s12f s12g s12h)
  -- 22. calculation
  have s22 : 1 / 2 * dist P X * dist Y M = 1 / 2 * dist P Y * dist X N := by
    calc 1 / 2 * dist P X * dist Y M = 1 / 2 * (dist P X * dist Y X) * abs (Real.sin (Complex.arg ((Y - X) / (P - X)))) := s16.symm
      _ = 1 / 2 * (dist P Y * dist X Y) * abs (Real.sin (Complex.arg ((X - Y) / (P - Y)))) := s8
      _ = 1 / 2 * dist P Y * dist X N := s20
  -- 23. algebra, from 21
  have s23 : 1 / 2 * dist P Q * dist Y M * dist P X = 1 / 2 * dist P R * dist X N * dist P X := by linear_combination ((16 * dist P X) / (((2 : ℝ)) * ((2 : ℝ)) * (4))) * s21
  -- 24. algebra, from 22
  have s24 : 1 / 2 * dist P X * dist Y M * dist P Q = 1 / 2 * dist P Y * dist X N * dist P Q := by linear_combination ((16 * dist P Q) / (((2 : ℝ)) * ((2 : ℝ)) * (4))) * s22
  -- 25. algebra, from 23, 24
  have s25 : 1 / 2 * dist P X * dist P R * dist X N = 1 / 2 * dist P Y * dist P Q * dist X N := by linear_combination ((-16) / (((2 : ℝ)) * ((2 : ℝ)) * (4))) * s23 + ((16) / (((2 : ℝ)) * ((2 : ℝ)) * (4))) * s24
  -- 26. axi:distance-positive P := X, Q := N, from 12
  have s26 : dist X N > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := X) (Q := N) s12f)
  -- 27. mun:multiply-cancel a := (1/2)·|PX|·|PR|, b := (1/2)·|PY|·|PQ|, c := |XN|, from 25
  have r4151_1 : dist X N ≠ 0 := ne_of_gt (by linarith only [s26])
  have s27 : 1 / 2 * dist P X * dist P R = 1 / 2 * dist P Y * dist P Q := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 1 / 2 * dist P X * dist P R) (b := 1 / 2 * dist P Y * dist P Q) (c := dist X N) s25 r4151_1)
  -- 28. algebra, from 27
  linear_combination ((8) / ((4))) * s27

end Parley.Stdlib.Geometry.ProportionalSegments

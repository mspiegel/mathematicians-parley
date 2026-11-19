module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
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
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.OffLineAlong
public import Parley.Stdlib.Geometry.ParallelOff

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.ParallelBetween

theorem parallel_between (P : ℂ) (Q : ℂ) (R : ℂ) (X : ℂ) (Y : ℂ) (hH6 : LeanBridges.Geometry.Triangle P Q R) (hH7 : Sbtw ℝ P X Q) (hH8 : Y ∈ LeanBridges.Geometry.line P R) (hH9 : 0 < Complex.im ((Y - P) / (Q - P)) * Complex.im ((R - P) / (Q - P))) (hH10 : Complex.im ((Y - X) / (R - Q)) = 0) :
    Sbtw ℝ P Y R := by
  -- 1. mun:same-side-off-line A := P, B := Q, P := Y, Q := R, from H9
  have s1 : ¬ Y ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := P) (B := Q) (P := Y) (Q := R) hH9)
  -- 2. mun:on-line-ends A := P, B := Q, from H6
  have s2a : P ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := P) (B := Q) hH6.1)
  have s2b : Q ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := P) (B := Q) hH6.1)
  -- 3. mun:triangle-on-side P := R, R := P, S := X, from H6, H7
  have s3 : LeanBridges.Geometry.Triangle R Q X := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := R) (Q := Q) (R := P) (S := X) (by (have h := hH6; rw [LeanBridges.Geometry.triangle_swap_13 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R Q P) (by (have h := hH7; rw [sbtw_comm (x := P) (y := X) (z := Q)] at h; exact h) : Sbtw ℝ Q X P))
  -- 4. mun:triangle-not-on-line P := X, from 3
  have s4 : ¬ X ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := X) (Q := Q) (R := R) (by (have h := s3; rw [LeanBridges.Geometry.triangle_swap_13 R Q X] at h; exact h) : LeanBridges.Geometry.Triangle X Q R))
  -- 5. mun:between-collinear R := X, S := P, T := Q, from H7
  have s5 : Collinear ℝ {Q, X, P} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := X) (S := P) (T := Q) hH7)
  -- 6. def:on-line P := X, A := P, B := Q, from H6, 5
  have s6 : X ∈ LeanBridges.Geometry.line P Q := ((Parley.Items.Stdlib.Geometry.def_on_line (A := P) (B := Q) (P := X) hH6.1)).mpr (by (have h := s5; rw [LeanBridges.Geometry.collinear_rot_312 Q X P] at h; exact h) : Collinear ℝ {P, Q, X})
  -- 7. mun:on-off-apart A := P, B := Q, from 1, 6
  have s7 : X ≠ Y := by exact (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := P) (B := Q) (X := X) (Y := Y) s6 s1)
  -- 8. mun:on-line-ends A := X, B := Y, from 7
  have s8a : X ∈ LeanBridges.Geometry.line X Y := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := X) (B := Y) s7)
  have s8b : Y ∈ LeanBridges.Geometry.line X Y := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := X) (B := Y) s7)
  -- 9. mun:parallel-off A := X, B := Y, C := Q, D := R, X := Y, from H6, H10, 4, 7, 8
  have s9 : ¬ Y ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Stdlib.Geometry.ParallelOff.parallel_off (A := X) (B := Y) (C := Q) (D := R) (X := Y) s7 hH6.2.1 hH10 s4 s8b)
  -- 10. mun:between-apart R := X, S := P, T := Q, from H7
  have s10a : P ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := X) (S := P) (T := Q) hH7)
  have s10b : Q ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := X) (S := P) (T := Q) hH7)
  -- 11. mun:same-side-of-line A := P, B := Q, C := X, D := Q, P := Y, Q := R, from H6, H9, 2, 3, 6
  have s11 : 0 < Complex.im ((Y - X) / (Q - X)) * Complex.im ((R - X) / (Q - X)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_of_line (A := P) (B := Q) (C := X) (D := Q) (P := Y) (Q := R) hH6.1 (Ne.symm s3.2.1) s6 s2b hH9)
  -- 12. mun:same-side-off-line A := X, B := Q, P := Y, Q := R, from 11
  have s12 : ¬ Y ∈ LeanBridges.Geometry.line X Q := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := X) (B := Q) (P := Y) (Q := R) s11)
  -- 13. def:on-line A := X, B := Q, from 3, 5
  have s13 : P ∈ LeanBridges.Geometry.line X Q := ((Parley.Items.Stdlib.Geometry.def_on_line (A := X) (B := Q) (P := P) (Ne.symm s3.2.1))).mpr (by (have h := s5; rw [LeanBridges.Geometry.collinear_swap_12 Q X P] at h; exact h) : Collinear ℝ {X, Q, P})
  -- 14. mun:off-line-along A := X, B := Q, X := P, P := Y, from 10, 12, 13
  have s14 : ¬ Y ∈ LeanBridges.Geometry.line X P := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := X) (B := Q) (X := P) (P := Y) (Ne.symm s10b) s13 s10a s12)
  -- 15. mun:off-line-swap R := X, Q := Y, from 10, 14
  have s15 : ¬ P ∈ LeanBridges.Geometry.line X Y := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_swap (P := P) (Q := Y) (R := X) (Ne.symm s10a) s14)
  -- 16. mun:segment-across-line A := X, B := Y, M := X, from H7, 7, 8, 15
  have s16 : Complex.im ((P - X) / (Y - X)) * Complex.im ((Q - X) / (Y - X)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := X) (B := Y) (M := X) (P := P) (Q := Q) s7 s8a s15 hH7)
  -- 17. mun:on-line-cases P := Y, Q := P, from H6, H8
  have s17 : (((Y = P ∨ Sbtw ℝ P Y R) ∨ Y = R) ∨ Sbtw ℝ P R Y) ∨ Sbtw ℝ Y P R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := Y) (Q := P) (R := R) hH6.2.2.1 hH8)
  -- 18. cases, from 17
  rcases s17 with (((hC1 | hC2) | hC3) | hC4) | hC5
  · skip
    -- 18.1. substitute Y = P (C1) into line 1
    have s18_1 : ¬ P ∈ LeanBridges.Geometry.line P Q := Eq.subst (motive := (fun t : ℂ => ¬ t ∈ LeanBridges.Geometry.line P Q)) hC1 s1
    exact absurd s2a s18_1
  · skip
    -- 18.2. restate C2
    exact hC2
  · skip
    -- 18.3. mun:on-line-ends A := Q, B := R, from H6
    have s18_3 : R ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := Q) (B := R) hH6.2.1)
    -- 18.4. substitute Y = R (C3) into line 9
    have s18_4 : ¬ R ∈ LeanBridges.Geometry.line Q R := Eq.subst (motive := (fun t : ℂ => ¬ t ∈ LeanBridges.Geometry.line Q R)) hC3 s9
    exact absurd s18_3 s18_4
  · skip
    -- 18.5. restate 8
    have s18_5 : Y ∈ LeanBridges.Geometry.line X Y := by exact s8b
    -- 18.6. mun:segment-off-line A := X, B := Y, Q := Y, X := R, from C4, 7, 15, 18.5
    have s18_6 : 0 < Complex.im ((R - X) / (Y - X)) * Complex.im ((P - X) / (Y - X)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := X) (B := Y) (P := P) (Q := Y) (X := R) s7 s18_5 s15 hC4)
    -- 18.7. mun:same-opposite-opposite A := X, B := Y, P := R, Q := P, R := Q, from 16, 18.6
    have s18_7 : Complex.im ((R - X) / (Y - X)) * Complex.im ((Q - X) / (Y - X)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := X) (B := Y) (P := R) (Q := P) (R := Q) s18_6 s16)
    -- 18.8. obtain Z: axi:plane-separation-crossing A := X, B := Y, P := R, from 7, 18.7
    obtain ⟨Z, s18_8a, ⟨s18_8b, s18_8c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_plane_separation_crossing (A := X) (B := Y) (P := R) (Q := Q) s7 s18_7)
    -- 18.9. mun:between-collinear R := Z, S := R, T := Q, from 18.8
    have s18_9 : Collinear ℝ {Q, Z, R} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := Z) (S := R) (T := Q) s18_8c)
    -- 18.10. def:on-line P := Z, A := Q, B := R, from H6, 18.9
    have s18_10 : Z ∈ LeanBridges.Geometry.line Q R := ((Parley.Items.Stdlib.Geometry.def_on_line (A := Q) (B := R) (P := Z) hH6.2.1)).mpr (by (have h := s18_9; rw [LeanBridges.Geometry.collinear_swap_23 Q Z R] at h; exact h) : Collinear ℝ {Q, R, Z})
    -- 18.11. mun:parallel-off A := X, B := Y, C := Q, D := R, X := Z, from H6, H10, 4, 7, 18.8
    have s18_11 : ¬ Z ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Stdlib.Geometry.ParallelOff.parallel_off (A := X) (B := Y) (C := Q) (D := R) (X := Z) s7 hH6.2.1 hH10 s4 s18_8b)
    exact absurd s18_10 s18_11
  · skip
    -- 18.12. mun:segment-across-line A := P, B := Q, P := Y, Q := R, M := P, from C5, H6, 1, 2
    have s18_12 : Complex.im ((Y - P) / (Q - P)) * Complex.im ((R - P) / (Q - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := P) (B := Q) (M := P) (P := Y) (Q := R) hH6.1 s2a s1 hC5)
    -- 18.13. mun:same-not-opposite A := P, B := Q, P := Y, Q := R, from H9
    have s18_13 : ¬ Complex.im ((Y - P) / (Q - P)) * Complex.im ((R - P) / (Q - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_not_opposite (A := P) (B := Q) (P := Y) (Q := R) hH9)
    exact absurd s18_12 s18_13

end Parley.Stdlib.Geometry.ParallelBetween

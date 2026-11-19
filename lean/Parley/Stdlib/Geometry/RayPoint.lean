module

public import Geometry
public import Mathlib.Algebra.Group.Semigroup
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
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
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

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.RayPoint

theorem ray_point (A : ℂ) (B : ℂ) (C : ℂ) (r : ℝ) (hH5 : LeanBridges.Geometry.Triangle A B C) (hH6 : r > 0) :
    (∃ X ∈ (Set.univ : Set ℂ), (X ∈ LeanBridges.Geometry.line A B ∧ 0 < Complex.im ((X - A) / (C - A)) * Complex.im ((B - A) / (C - A))) ∧ dist A X = r) := by
  -- 1. mun:triangle-not-on-line P := B, Q := A, R := C, from H5
  have s1 : ¬ B ∈ LeanBridges.Geometry.line A C := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := B) (Q := A) (R := C) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C))
  -- 2. mun:on-line-ends B := C, from H5
  have s2 : A ∈ LeanBridges.Geometry.line A C := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := C) hH5.2.2.1)
  -- 3. mun:on-line-ends, from H5
  have s3 : B ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := A) (B := B) hH5.1)
  -- 4. axi:trichotomy x := r − |AB|
  have s4 : (r - dist A B < 0 ∨ r - dist A B = 0) ∨ 0 < r - dist A B := by exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := r - dist A B))
  -- 5. cases, from 4
  rcases s4 with (hC1 | hC2) | hC3
  · skip
    -- 5.1. inequalities
    have s5_1 : r < dist A B := by linarith only [hC1]
    -- 5.2. obtain X: mun:segment-point, from H6, 5.1
    obtain ⟨X, s5_2a, ⟨s5_2b, s5_2c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_point (A := A) (B := B) (r := r) hH6 s5_1)
    -- 5.3. mun:segment-off-line B := C, P := B, Q := A, from H5, 1, 2, 5.2
    have s5_3 : 0 < Complex.im ((X - A) / (C - A)) * Complex.im ((B - A) / (C - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := A) (B := C) (P := B) (Q := A) (X := X) hH5.2.2.1 s2 s1 (by (have h := s5_2b; rw [sbtw_comm (x := A) (y := X) (z := B)] at h; exact h) : Sbtw ℝ B X A))
    -- 5.4. mun:between-collinear R := X, S := A, T := B, from 5.2
    have s5_4 : Collinear ℝ {B, X, A} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := X) (S := A) (T := B) s5_2b)
    -- 5.5. def:on-line P := X, from H5, 5.4
    have s5_5 : X ∈ LeanBridges.Geometry.line A B := ((Parley.Items.Stdlib.Geometry.def_on_line (A := A) (B := B) (P := X) hH5.1)).mpr (by (have h := s5_4; rw [LeanBridges.Geometry.collinear_rot_312 B X A] at h; exact h) : Collinear ℝ {A, B, X})
    -- 5.6. exhibit, from 5.2, 5.3, 5.5
    exact ⟨X, Set.mem_univ _, ⟨⟨s5_5, s5_3⟩, s5_2c⟩⟩
  · skip
    -- 5.7. algebra, from C2
    have s5_7 : dist A B = r := by linear_combination (-1) * hC2
    -- 5.8. obtain M: mun:midpoint-exists, from H5
    obtain ⟨M, s5_8a, s5_8b⟩ := (Parley.Items.Stdlib.Geometry.mun_midpoint_exists (A := A) (B := B) hH5.1)
    -- 5.9. def:midpoint, from 5.8
    have s5_9a : Sbtw ℝ A M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp s5_8b).1
    have s5_9b : dist A M = dist M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp s5_8b).2
    -- 5.10. mun:segment-off-line B := C, P := B, Q := A, X := M, from H5, 1, 2, 5.9
    have s5_10 : 0 < Complex.im ((M - A) / (C - A)) * Complex.im ((B - A) / (C - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := A) (B := C) (P := B) (Q := A) (X := M) hH5.2.2.1 s2 s1 (by (have h := s5_9a; rw [sbtw_comm (x := A) (y := M) (z := B)] at h; exact h) : Sbtw ℝ B M A))
    -- 5.11. mun:same-side-same B := C, P := B, Q := M, R := B, from 5.10
    have s5_11 : 0 < Complex.im ((B - A) / (C - A)) * Complex.im ((B - A) / (C - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := A) (B := C) (P := B) (Q := M) (R := B) (by (have h := s5_10; rw [mul_comm (Complex.im ((M - A) / (C - A))) (Complex.im ((B - A) / (C - A)))] at h; exact h) : 0 < Complex.im ((B - A) / (C - A)) * Complex.im ((M - A) / (C - A))) s5_10)
    -- 5.12. exhibit, from 3, 5.7, 5.11
    exact ⟨B, Set.mem_univ _, ⟨⟨s3, s5_11⟩, s5_7⟩⟩
  · skip
    -- 5.13. inequalities
    have s5_13 : r - dist A B > 0 := by linarith only [hC3]
    -- 5.14. obtain X: mun:segment-extension r := r − |AB|, from H5, 5.13
    obtain ⟨X, s5_14a, ⟨s5_14b, s5_14c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := A) (B := B) (r := r - dist A B) hH5.1 s5_13)
    -- 5.15. mun:segment-addition P := A, Q := X, S := B, from 5.14
    have s5_15 : dist A B + dist B X = dist A X := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := X) (S := B) s5_14b)
    -- 5.16. algebra, from 5.14, 5.15
    have s5_16 : dist A X = r := by linear_combination s5_14c + (-1) * s5_15
    -- 5.17. mun:between-collinear R := B, S := A, T := X, from 5.14
    have s5_17 : Collinear ℝ {X, B, A} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := B) (S := A) (T := X) s5_14b)
    -- 5.18. def:on-line P := X, from H5, 5.17
    have s5_18 : X ∈ LeanBridges.Geometry.line A B := ((Parley.Items.Stdlib.Geometry.def_on_line (A := A) (B := B) (P := X) hH5.1)).mpr (by (have h := s5_17; rw [LeanBridges.Geometry.collinear_swap_13 X B A] at h; exact h) : Collinear ℝ {A, B, X})
    -- 5.19. mun:segment-beyond-off-line B := C, P := X, Q := A, X := B, from H5, 1, 2, 5.14
    have s5_19 : 0 < Complex.im ((X - A) / (C - A)) * Complex.im ((B - A) / (C - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_beyond_off_line (A := A) (B := C) (P := X) (Q := A) (X := B) hH5.2.2.1 s2 s1 (by (have h := s5_14b; rw [sbtw_comm (x := A) (y := B) (z := X)] at h; exact h) : Sbtw ℝ X B A))
    -- 5.20. exhibit, from 5.16, 5.18, 5.19
    exact ⟨X, Set.mem_univ _, ⟨⟨s5_18, s5_19⟩, s5_16⟩⟩

end Parley.Stdlib.Geometry.RayPoint

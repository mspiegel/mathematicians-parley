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
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.OffLineAlong

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.CrossingTriangle

theorem crossing_triangle (D : ℂ) (E : ℂ) (F : ℂ) (G : ℂ) (X : ℂ) (hH6 : LeanBridges.Geometry.Triangle D E F) (hH7 : X ∈ LeanBridges.Geometry.line E F) (hH8 : Sbtw ℝ D X G) (hH9 : X ≠ E) :
    LeanBridges.Geometry.Triangle D G E := by
  -- 1. mun:triangle-not-on-line P := D, Q := E, R := F, from H6
  have s1 : ¬ D ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := D) (Q := E) (R := F) hH6)
  -- 2. mun:off-line-along A := E, B := F, P := D, from H6, H7, H9, 1
  have s2 : ¬ D ∈ LeanBridges.Geometry.line E X := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := E) (B := F) (X := X) (P := D) hH6.2.1 hH7 hH9 s1)
  -- 3. mun:triangle-off-line P := D, Q := E, R := X, from H9, 2
  have s3 : LeanBridges.Geometry.Triangle D E X := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := D) (Q := E) (R := X) (Ne.symm hH9) s2)
  -- 4. mun:triangle-not-on-line P := X, Q := D, R := E, from 3
  have s4 : ¬ X ∈ LeanBridges.Geometry.line D E := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := X) (Q := D) (R := E) (by (have h := s3; rw [LeanBridges.Geometry.triangle_rot_312 D E X] at h; exact h) : LeanBridges.Geometry.Triangle X D E))
  -- 5. mun:on-line-ends A := D, B := E, from H6
  have s5 : D ∈ LeanBridges.Geometry.line D E := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := D) (B := E) hH6.1)
  -- 6. mun:segment-beyond-off-line A := D, B := E, P := G, Q := D, from H6, H8, 4, 5
  have s6 : 0 < Complex.im ((G - D) / (E - D)) * Complex.im ((X - D) / (E - D)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_beyond_off_line (A := D) (B := E) (P := G) (Q := D) (X := X) hH6.1 s5 s4 (by (have h := hH8; rw [sbtw_comm (x := D) (y := X) (z := G)] at h; exact h) : Sbtw ℝ G X D))
  -- 7. mun:same-side-off-line A := D, B := E, P := G, Q := X, from 6
  have s7 : ¬ G ∈ LeanBridges.Geometry.line D E := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := D) (B := E) (P := G) (Q := X) s6)
  -- 8. mun:off-line-swap R := D, P := E, Q := G, from H6, 7
  have s8 : ¬ E ∈ LeanBridges.Geometry.line D G := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_swap (P := E) (Q := G) (R := D) hH6.1 s7)
  -- 9. mun:between-ends-apart R := X, S := D, T := G, from H8
  have s9 : D ≠ G := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := X) (S := D) (T := G) hH8)
  -- 10. mun:triangle-off-line P := E, Q := D, R := G, from 8, 9
  have s10 : LeanBridges.Geometry.Triangle E D G := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := E) (Q := D) (R := G) s9 s8)
  exact (by (have h := s10; rw [LeanBridges.Geometry.triangle_rot_231 E D G] at h; exact h) : LeanBridges.Geometry.Triangle D G E)

end Parley.Stdlib.Geometry.CrossingTriangle

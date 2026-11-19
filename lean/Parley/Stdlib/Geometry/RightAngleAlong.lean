module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.RightAngleAlong

theorem right_angle_along (P : ℂ) (H : ℂ) (S : ℂ) (T : ℂ) (hH5 : P ≠ H) (hH6 : S ≠ H) (hH7 : EuclideanGeometry.angle P H S = (90 : ℝ) * Real.pi / 180) (hH8 : T ∈ LeanBridges.Geometry.line H S) (hH9 : T ≠ H) (hH10 : P ≠ S) (hH11 : LeanBridges.Geometry.Triangle P H T) :
    EuclideanGeometry.angle P H T = (90 : ℝ) * Real.pi / 180 := by
  -- 1. mun:on-line-cases P := T, Q := H, R := S, from H6, H8
  have s1 : (((T = H ∨ Sbtw ℝ H T S) ∨ T = S) ∨ Sbtw ℝ H S T) ∨ Sbtw ℝ T H S := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := T) (Q := H) (R := S) (Ne.symm hH6) hH8)
  -- 2. mun:angle-turned Q := H, R := T, from H11
  have s2 : EuclideanGeometry.angle P H T = EuclideanGeometry.angle T H P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P) (Q := H) (R := T) hH11.1 (Ne.symm hH11.2.1) hH11.2.2.1)
  -- 3. mun:angle-turned P := S, Q := H, R := P, from H5, H6, H10
  have s3 : EuclideanGeometry.angle S H P = EuclideanGeometry.angle P H S := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := S) (Q := H) (R := P) hH6 hH5 (Ne.symm hH10))
  -- 4. cases, from 1
  rcases s1 with (((hC1 | hC2) | hC3) | hC4) | hC5
  · skip
    -- 4.1. restate H9
    have s4_1 : T ≠ H := by exact hH9
    exact absurd hC1 s4_1
  · skip
    -- 4.2. calculation
    calc EuclideanGeometry.angle P H T = EuclideanGeometry.angle T H P := s2
      _ = EuclideanGeometry.angle S H P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := H) (Q := S) (R := P) (S := T) hC2 hH11.1 hH11.2.2.1 hH10)
      _ = EuclideanGeometry.angle P H S := s3
      _ = (90 : ℝ) * Real.pi / 180 := hH7
  · skip
    -- 4.3. substitute T = S (C3) into H7
    exact Eq.subst (motive := (fun t : ℂ => EuclideanGeometry.angle P H t = (90 : ℝ) * Real.pi / 180)) hC3.symm hH7
  · skip
    -- 4.4. calculation
    calc EuclideanGeometry.angle P H T = EuclideanGeometry.angle T H P := s2
      _ = EuclideanGeometry.angle S H P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := H) (Q := T) (R := P) (S := S) hC4 hH11.1 hH10 hH11.2.2.1).symm
      _ = EuclideanGeometry.angle P H S := s3
      _ = (90 : ℝ) * Real.pi / 180 := hH7
  · skip
    -- 4.5. axi:supplementary-angles A := T, B := H, C := S, D := P, from C5, H10, H11
    have s4_5 : EuclideanGeometry.angle T H P + EuclideanGeometry.angle P H S = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := T) (B := H) (C := S) (D := P) hC5 hH11.1 hH11.2.2.1 hH10)
    -- 4.6. algebra, from H7, 2, 4.5
    linear_combination ((-32400) / ((180) * (180))) * hH7 + ((180) / ((180))) * s2 + ((32400) / ((180) * (180))) * s4_5

end Parley.Stdlib.Geometry.RightAngleAlong

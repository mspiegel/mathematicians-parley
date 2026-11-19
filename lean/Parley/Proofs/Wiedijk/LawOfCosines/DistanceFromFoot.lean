module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
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
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Trigonometry
public import Parley.Proofs.Wiedijk.LawOfCosines.FootOnRay

/-! Written from proofs/wiedijk/law-of-cosines.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LawOfCosines.DistanceFromFoot

theorem distance_from_foot (P : ℂ) (Q : ℂ) (R : ℂ) (H : ℂ) (hH5 : LeanBridges.Geometry.Triangle P Q R) (hH6 : H ∈ LeanBridges.Geometry.line Q R) (hH7 : P ≠ H) (hH8 : H ≠ Q → EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180) (hH9 : H ≠ R → EuclideanGeometry.angle P H R = (90 : ℝ) * Real.pi / 180) :
    dist H R ^ 2 = dist H Q ^ 2 + dist Q R ^ 2 - 2 * (dist P Q * dist Q R * Real.cos (EuclideanGeometry.angle P Q R)) := by
  -- 1. mun:on-line-cases P := H, from H5, H6
  have s1 : (((H = Q ∨ Sbtw ℝ Q H R) ∨ H = R) ∨ Sbtw ℝ Q R H) ∨ Sbtw ℝ H Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := H) (Q := Q) (R := R) hH5.2.1 hH6)
  -- 2. cases, from 1
  rcases s1 with (((hC1 | hC2) | hC3) | hC4) | hC5
  · skip
    -- 2.1. substitute Q = H (C1) into H5
    have s2_1 : H ≠ R := Eq.subst (motive := (fun t : ℂ => t ≠ R)) hC1.symm hH5.2.1
    -- 2.2. mun:modus-ponens, from H9, 2.1
    have s2_2 : EuclideanGeometry.angle P H R = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ R) (Q := EuclideanGeometry.angle P H R = (90 : ℝ) * Real.pi / 180) hH9 s2_1)
    -- 2.3. substitute H = Q (C1) into line 2.2
    have s2_3 : EuclideanGeometry.angle P Q R = (90 : ℝ) * Real.pi / 180 := Eq.subst (motive := (fun t : ℂ => EuclideanGeometry.angle P t R = (90 : ℝ) * Real.pi / 180)) hC1 s2_2
    -- 2.4. mun:right-angle-by-cosine, from H5, 2.3
    have s2_4 : Real.cos (EuclideanGeometry.angle P Q R) = 0 := by exact ((Parley.Items.Stdlib.Geometry.mun_right_angle_by_cosine (P := P) (Q := Q) (R := R) hH5.1 (Ne.symm hH5.2.1) hH5.2.2.1)).mp s2_3
    -- 2.5. mun:distance-zero P := H, from C1
    have s2_5 : dist H Q = 0 := ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := H) (Q := Q))).mpr hC1
    -- 2.6. calculation
    calc dist H R ^ 2 = dist Q R ^ 2 := by (have h := congrArg (fun t : ℂ => (dist t R : ℂ) ^ 2) hC1; push_cast at h ⊢; exact_mod_cast h)
      _ = dist H Q ^ 2 + dist Q R ^ 2 := by linear_combination (-dist H Q) * s2_5
      _ = dist H Q ^ 2 + dist Q R ^ 2 - 2 * (dist P Q * dist Q R * Real.cos (EuclideanGeometry.angle P Q R)) := by linear_combination (2 * dist P Q * dist Q R) * s2_4
  · skip
    -- 2.7. mun:between-apart R := H, S := Q, T := R, from C2
    have s2_7a : Q ≠ H := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := H) (S := Q) (T := R) hC2)
    have s2_7b : R ≠ H := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := H) (S := Q) (T := R) hC2)
    -- 2.8. mun:modus-ponens, from H8, 2.7
    have s2_8 : EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ Q) (Q := EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180) hH8 (Ne.symm s2_7a))
    -- 2.9. mun:angle-along-segment P := Q, Q := R, R := P, S := H, from C2, H5
    have r154_1 : P ≠ H := by exact hH7
    have s2_9 : EuclideanGeometry.angle H Q P = EuclideanGeometry.angle R Q P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := Q) (Q := R) (R := P) (S := H) hC2 hH5.1 r154_1 hH5.2.2.1)
    -- 2.10. mun:segment-addition P := Q, Q := R, S := H, from C2
    have s2_10 : dist Q H + dist H R = dist Q R := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := Q) (Q := R) (S := H) hC2)
    -- 2.11. algebra, from 2.10
    have s2_11 : dist H R ^ 2 = (dist Q R - dist Q H) ^ 2 := by linear_combination (-dist Q H + dist H R + dist Q R) * s2_10
    -- 2.12. thm:foot-on-ray, from H5, H7, 2.7, 2.8, 2.9, 2.11
    exact (Parley.Proofs.Wiedijk.LawOfCosines.FootOnRay.foot_on_ray (P := P) (Q := Q) (R := R) (H := H) hH5 hH7 s2_7a s2_8 s2_9 s2_11)
  · skip
    -- 2.13. substitute R = H (C3) into H5
    have s2_13 : Q ≠ H := Eq.subst (motive := (fun t : ℂ => Q ≠ t)) hC3.symm hH5.2.1
    -- 2.14. mun:modus-ponens, from H8, 2.13
    have s2_14 : EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ Q) (Q := EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180) hH8 (Ne.symm s2_13))
    -- 2.15. substitute H = R (C3)
    have s2_15 : EuclideanGeometry.angle H Q P = EuclideanGeometry.angle R Q P := by (have h := congrArg (fun t : ℂ => (EuclideanGeometry.angle t Q P : ℂ)) hC3; push_cast at h ⊢; exact_mod_cast h)
    -- 2.16. mun:distance-zero P := H, Q := R, from C3
    have s2_16 : dist H R = 0 := ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := H) (Q := R))).mpr hC3
    -- 2.17. algebra, from 2.16
    have s2_17 : dist H R ^ 2 = (dist Q R - dist Q R) ^ 2 := by linear_combination (dist H R) * s2_16
    -- 2.18. substitute R = H (C3) into line 2.17
    have s2_18 : dist H R ^ 2 = (dist Q R - dist Q H) ^ 2 := Eq.subst (motive := (fun t : ℂ => dist H R ^ 2 = (dist Q R - dist Q t) ^ 2)) hC3.symm s2_17
    -- 2.19. thm:foot-on-ray, from H5, H7, 2.13, 2.14, 2.15, 2.18
    exact (Parley.Proofs.Wiedijk.LawOfCosines.FootOnRay.foot_on_ray (P := P) (Q := Q) (R := R) (H := H) hH5 hH7 s2_13 s2_14 s2_15 s2_18)
  · skip
    -- 2.20. mun:between-ends-apart S := Q, T := H, from C4
    have s2_20 : Q ≠ H := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := R) (S := Q) (T := H) hC4)
    -- 2.21. mun:modus-ponens, from H8, 2.20
    have s2_21 : EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ Q) (Q := EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180) hH8 (Ne.symm s2_20))
    -- 2.22. mun:angle-along-segment P := Q, Q := H, R := P, S := R, from C4, H5
    have r200_1 : P ≠ H := by exact hH7
    have s2_22 : EuclideanGeometry.angle R Q P = EuclideanGeometry.angle H Q P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := Q) (Q := H) (R := P) (S := R) hC4 hH5.1 hH5.2.2.1 r200_1)
    -- 2.23. mun:segment-addition P := Q, Q := H, S := R, from C4
    have s2_23 : dist Q R + dist R H = dist Q H := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := Q) (Q := H) (S := R) hC4)
    -- 2.24. algebra, from 2.23
    have s2_24 : dist H R ^ 2 = (dist Q R - dist Q H) ^ 2 := by
      rw [dist_comm Q H, dist_comm R H] at s2_23
      rw [dist_comm Q H]
      exact (by linear_combination (dist H Q + dist H R - dist Q R) * s2_23)
    -- 2.25. thm:foot-on-ray, from H5, H7, 2.20, 2.21, 2.22, 2.24
    exact (Parley.Proofs.Wiedijk.LawOfCosines.FootOnRay.foot_on_ray (P := P) (Q := Q) (R := R) (H := H) hH5 hH7 s2_20 s2_21 s2_22.symm s2_24)
  · skip
    -- 2.26. mun:between-apart R := Q, S := H, T := R, from C5
    have s2_26a : H ≠ Q := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := Q) (S := H) (T := R) hC5)
    have s2_26b : R ≠ Q := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := Q) (S := H) (T := R) hC5)
    -- 2.27. mun:modus-ponens, from H8, 2.26
    have s2_27 : EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ Q) (Q := EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180) hH8 s2_26a)
    -- 2.28. mun:cosine-right-triangle R := H, from H5, H7, 2.26, 2.27
    have s2_28 : dist Q H = dist Q P * Real.cos (EuclideanGeometry.angle H Q P) := by exact (Parley.Items.Stdlib.Geometry.mun_cosine_right_triangle (P := P) (Q := Q) (R := H) hH7 (Ne.symm s2_26a) s2_27 hH5.1)
    -- 2.29. axi:supplementary-angles A := H, B := Q, C := R, D := P, from C5, H5
    have r226_1 : P ≠ H := by exact hH7
    have s2_29 : EuclideanGeometry.angle H Q P + EuclideanGeometry.angle P Q R = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := H) (B := Q) (C := R) (D := P) hC5 hH5.1 r226_1 hH5.2.2.1)
    -- 2.30. substitute
    have s2_30 : dist Q H = dist Q P * Real.cos ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle P Q R) := by
      have c1 : EuclideanGeometry.angle H Q P = (180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle P Q R := by linear_combination ((32400) / ((180) * (180))) * s2_29
      have row1 : dist Q H = dist Q P * Real.cos ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle P Q R) := Eq.subst (motive := (fun t : ℝ => dist Q H = dist Q P * Real.cos t)) c1 s2_28
      exact row1
    -- 2.31. substitute
    have s2_31 : dist Q H = dist Q P * -Real.cos (EuclideanGeometry.angle P Q R) := by
      have c1 : Real.cos ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle P Q R) = -Real.cos (EuclideanGeometry.angle P Q R) := by exact (Parley.Items.Stdlib.Trigonometry.mun_cos_supplement (x := EuclideanGeometry.angle P Q R))
      have row1 : dist Q H = dist Q P * -Real.cos (EuclideanGeometry.angle P Q R) := Eq.subst (motive := (fun t : ℝ => dist Q H = dist Q P * t)) c1 s2_30
      exact row1
    -- 2.32. mun:segment-addition P := H, Q := R, S := Q, from C5
    have s2_32 : dist H Q + dist Q R = dist H R := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := H) (Q := R) (S := Q) hC5)
    -- 2.33. algebra, from 2.32
    have s2_33 : dist H R ^ 2 = dist H Q ^ 2 + dist Q R ^ 2 + 2 * (dist Q R * dist Q H) := by
      rw [dist_comm Q H]
      exact (by linear_combination (-dist H Q - dist H R - dist Q R) * s2_32)
    -- 2.34. substitute |QH| = |QP|·−cos(∠PQR) (line 2.31) into line 2.33
    have s2_34 : dist H R ^ 2 = dist H Q ^ 2 + dist Q R ^ 2 + 2 * (dist Q R * (dist Q P * -Real.cos (EuclideanGeometry.angle P Q R))) := Eq.subst (motive := (fun t : ℝ => dist H R ^ 2 = dist H Q ^ 2 + dist Q R ^ 2 + 2 * (dist Q R * t))) s2_31 s2_33
    -- 2.35. algebra, from 2.34
    rw [dist_comm Q P] at s2_34
    exact (by linear_combination s2_34)

end Parley.Proofs.Wiedijk.LawOfCosines.DistanceFromFoot

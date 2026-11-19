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
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.Pythagoras.Pythagoras
public import Parley.Stdlib.Geometry.AngleSum
public import Parley.Stdlib.Geometry.PerpendicularFoot

/-! Written from proofs/euclid/acute-angle-by-squares.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.AcuteAngleBySquares.AcuteAngleBySquares

theorem acute_angle_by_squares (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) :
    (EuclideanGeometry.angle A C B < (90 : ℝ) * Real.pi / 180 ↔ dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2) := by
  -- 1. obtain H: thm:perpendicular-foot P := A, Q := C, R := B, from H4
  obtain ⟨H, s1a, ⟨⟨⟨s1b, s1c⟩, s1d⟩, s1e⟩⟩ := (Parley.Stdlib.Geometry.PerpendicularFoot.perpendicular_foot (P := A) (Q := C) (R := B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B))
  -- 2. axi:distance-positive P := B, Q := C, from H4
  have s2 : dist B C > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := B) (Q := C) hH4.2.1)
  -- 3. mun:angle-symmetric P := A, Q := C, R := B, from H4
  have s3 : EuclideanGeometry.angle A C B = EuclideanGeometry.angle B C A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := A) (Q := C) (R := B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B))
  -- 4. axi:excluded-middle P := H = C
  have s4 : H = C ∨ H ≠ C := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := H = C))
  -- 5. cases, from 4
  rcases s4 with hC1 | hC2
  · skip
    -- 5.1. substitute C = H (C1) into H4
    have s5_1 : H ≠ B := by apply Ne.symm; (have h := Eq.subst (motive := (fun t : ℂ => B ≠ t)) hC1.symm hH4.2.1; push_cast at h ⊢; exact_mod_cast h)
    -- 5.2. mun:modus-ponens, from 1, 5.1
    have s5_2 : EuclideanGeometry.angle A H B = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ B) (Q := EuclideanGeometry.angle A H B = (90 : ℝ) * Real.pi / 180) s1e s5_1)
    -- 5.3. substitute H = C (C1) into line 5.2
    have s5_3 : EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180 := Eq.subst (motive := (fun t : ℂ => EuclideanGeometry.angle A t B = (90 : ℝ) * Real.pi / 180)) hC1 s5_2
    -- 5.4. thm:pythagoras, from H4, 5.3
    have s5_4 : dist A B ^ 2 = dist A C ^ 2 + dist B C ^ 2 := by exact (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := A) (B := B) (C := C) hH4 s5_3)
    -- 5.5. inequalities
    have s5_5 : EuclideanGeometry.angle A C B ≥ (90 : ℝ) * Real.pi / 180 := by linarith only [s5_3]
    -- 5.6. inequalities, from 5.5
    have s5_6 : ¬ EuclideanGeometry.angle A C B < (90 : ℝ) * Real.pi / 180 := by linarith only [s5_5]
    -- 5.7. inequalities
    have s5_7 : dist A B ^ 2 ≥ dist A C ^ 2 + dist B C ^ 2 := by linarith only [s5_4]
    -- 5.8. inequalities, from 5.7
    have s5_8 : ¬ dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2 := by linarith only [s5_7]
    -- 5.9. mun:iff-both-false, from 5.6, 5.8
    exact (Parley.Items.Stdlib.Reasoning.mun_iff_both_false (P := EuclideanGeometry.angle A C B < (90 : ℝ) * Real.pi / 180) (Q := dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2) s5_6 s5_8)
  · skip
    -- 5.10. mun:modus-ponens, from C2, 1
    have s5_10 : EuclideanGeometry.angle A H C = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ C) (Q := EuclideanGeometry.angle A H C = (90 : ℝ) * Real.pi / 180) s1d hC2)
    -- 5.11. mun:right-angle-triangle P := A, Q := H, R := C, from C2, H4, 1, 5.10
    have s5_11 : LeanBridges.Geometry.Triangle A H C := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := A) (Q := H) (R := C) s1c (Ne.symm hC2) s5_10 hH4.2.2.1)
    -- 5.12. thm:pythagoras B := C, C := H, from 5.10, 5.11
    have s5_12 : dist A C ^ 2 = dist A H ^ 2 + dist H C ^ 2 := (by (have h := (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := A) (B := C) (C := H) (by (have h := s5_11; rw [LeanBridges.Geometry.triangle_swap_23 A H C] at h; exact h) : LeanBridges.Geometry.Triangle A C H) s5_10); rw [dist_comm C H] at h; exact h) : dist A C ^ 2 = dist A H ^ 2 + dist H C ^ 2)
    -- 5.13. thm:angle-sum B := H, from 5.11
    have s5_13 : EuclideanGeometry.angle H A C + EuclideanGeometry.angle A H C + EuclideanGeometry.angle H C A = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Stdlib.Geometry.AngleSum.angle_sum (A := A) (B := H) (C := C) s5_11)
    -- 5.14. axi:angle-measure P := H, Q := A, R := C, from 5.11
    have s5_14 : EuclideanGeometry.angle H A C > (0 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_1 (P := H) (Q := A) (R := C) (by (have h := s5_11; rw [LeanBridges.Geometry.triangle_swap_12 A H C] at h; exact h) : LeanBridges.Geometry.Triangle H A C))
    -- 5.15. algebra, from 5.10, 5.13
    have s5_15 : EuclideanGeometry.angle H C A = (90 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle H A C := by linear_combination ((-32400) / ((180) * (180))) * s5_10 + ((32400) / ((180) * (180))) * s5_13
    -- 5.16. inequalities
    have s5_16 : (90 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle H A C < (90 : ℝ) * Real.pi / 180 := by linarith only [s5_14]
    -- 5.17. calculation
    have s5_17 : EuclideanGeometry.angle H C A < (90 : ℝ) * Real.pi / 180 := by
      calc EuclideanGeometry.angle H C A = (90 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle H A C := s5_15
        _ < (90 : ℝ) * Real.pi / 180 := s5_16
    -- 5.18. axi:distance-positive P := C, Q := H, from C2
    have s5_18 : dist C H > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := C) (Q := H) (Ne.symm hC2))
    -- 5.19. mun:product-positive x := |BC|, y := |CH|, from 2, 5.18
    have s5_19 : dist B C * dist C H > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_positive (x := dist B C) (y := dist C H) s2 s5_18)
    -- 5.20. inequalities
    have s5_20 : dist A C ^ 2 + dist B C ^ 2 - 2 * (dist B C * dist C H) < dist A C ^ 2 + dist B C ^ 2 := by linarith only [s5_19]
    -- 5.21. inequalities
    have s5_21 : dist A C ^ 2 + dist B C ^ 2 < dist A C ^ 2 + dist B C ^ 2 + 2 * (dist B C * dist C H) := by linarith only [s5_19]
    -- 5.22. mun:on-line-cases P := H, Q := C, R := B, from H4, 1
    have s5_22 : (((H = C ∨ Sbtw ℝ C H B) ∨ H = B) ∨ Sbtw ℝ C B H) ∨ Sbtw ℝ H C B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := H) (Q := C) (R := B) (Ne.symm hH4.2.1) s1b)
    -- 5.23. cases, from 5.22
    rcases s5_22 with (((hC3 | hC4) | hC5) | hC6) | hC7
    · skip
      -- 5.23.1. restate C2
      have s5_23_1 : H ≠ C := by exact hC2
      exact absurd hC3 s5_23_1
    · skip
      -- 5.23.2. mun:between-apart R := H, S := C, T := B, from C4
      have s5_23_2a : C ≠ H := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := H) (S := C) (T := B) hC4)
      have s5_23_2b : B ≠ H := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := H) (S := C) (T := B) hC4)
      -- 5.23.3. mun:modus-ponens, from 1, 5.23.2
      have s5_23_3 : EuclideanGeometry.angle A H B = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ B) (Q := EuclideanGeometry.angle A H B = (90 : ℝ) * Real.pi / 180) s1e (Ne.symm s5_23_2b))
      -- 5.23.4. mun:right-angle-triangle P := A, Q := H, R := B, from H4, 1, 5.23.2, 5.23.3
      have s5_23_4 : LeanBridges.Geometry.Triangle A H B := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := A) (Q := H) (R := B) s1c s5_23_2b s5_23_3 hH4.1)
      -- 5.23.5. thm:pythagoras C := H, from 5.23.3, 5.23.4
      have s5_23_5 : dist A B ^ 2 = dist A H ^ 2 + dist B H ^ 2 := by exact (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := A) (B := B) (C := H) (by (have h := s5_23_4; rw [LeanBridges.Geometry.triangle_swap_23 A H B] at h; exact h) : LeanBridges.Geometry.Triangle A B H) s5_23_3)
      -- 5.23.6. mun:segment-addition P := C, Q := B, S := H, from C4
      have s5_23_6 : dist C H + dist H B = dist C B := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := C) (Q := B) (S := H) hC4)
      -- 5.23.7. calculation
      have s5_23_7 : dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2 := by
        calc dist A B ^ 2 = dist A H ^ 2 + dist H B ^ 2 := (by (have h := s5_23_5; rw [dist_comm B H] at h; exact h) : dist A B ^ 2 = dist A H ^ 2 + dist H B ^ 2)
          _ = dist A C ^ 2 - dist H C ^ 2 + dist H B ^ 2 := by linear_combination (-1) * s5_12
          _ = dist A C ^ 2 - dist H C ^ 2 + (dist C B - dist C H) ^ 2 := by
              rw [dist_comm C B, dist_comm H B] at s5_23_6
              rw [dist_comm H B, dist_comm H C, dist_comm C B]
              exact (by linear_combination (dist B C + dist B H - dist C H) * s5_23_6)
          _ = dist A C ^ 2 + dist B C ^ 2 - 2 * (dist B C * dist C H) := by
              rw [dist_comm H C, dist_comm C B]
              exact (by ring1)
          _ < dist A C ^ 2 + dist B C ^ 2 := s5_20
      -- 5.23.8. mun:angle-along-segment P := C, Q := B, R := A, S := H, from C4, H4, 1
      have s5_23_8 : EuclideanGeometry.angle H C A = EuclideanGeometry.angle B C A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := C) (Q := B) (R := A) (S := H) hC4 hH4.2.2.1 s1c hH4.1)
      -- 5.23.9. calculation
      have s5_23_9 : EuclideanGeometry.angle A C B < (90 : ℝ) * Real.pi / 180 := by
        calc EuclideanGeometry.angle A C B = EuclideanGeometry.angle B C A := s3
          _ = EuclideanGeometry.angle H C A := s5_23_8.symm
          _ < (90 : ℝ) * Real.pi / 180 := s5_17
      -- 5.23.10. mun:iff-both-true, from 5.23.7, 5.23.9
      exact (Parley.Items.Stdlib.Reasoning.mun_iff_both_true (P := EuclideanGeometry.angle A C B < (90 : ℝ) * Real.pi / 180) (Q := dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2) s5_23_9 s5_23_7)
    · skip
      -- 5.23.11. substitute H = B (C5) into line 5.12
      have s5_23_11 : dist A C ^ 2 = dist A B ^ 2 + dist B C ^ 2 := Eq.subst (motive := (fun t : ℂ => dist A C ^ 2 = dist A t ^ 2 + dist t C ^ 2)) hC5 s5_12
      -- 5.23.12. calculation
      have s5_23_12 : dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2 := by
        calc dist A B ^ 2 = dist A C ^ 2 - dist B C ^ 2 := by linear_combination (-1) * s5_23_11
          _ = dist A C ^ 2 + dist B C ^ 2 - 2 * (dist B C * dist C B) := by
              rw [dist_comm C B]
              exact (by ring1)
          _ = dist A C ^ 2 + dist B C ^ 2 - 2 * (dist B C * dist C H) := by (have h := congrArg (fun t : ℂ => (dist A C : ℂ) ^ 2 + (dist B C : ℂ) ^ 2 - 2 * ((dist B C : ℂ) * (dist C t : ℂ))) hC5.symm; push_cast at h ⊢; exact_mod_cast h)
          _ < dist A C ^ 2 + dist B C ^ 2 := s5_20
      -- 5.23.13. substitute H = B (C5) into line 5.17
      have s5_23_13 : EuclideanGeometry.angle B C A < (90 : ℝ) * Real.pi / 180 := Eq.subst (motive := (fun t : ℂ => EuclideanGeometry.angle t C A < (90 : ℝ) * Real.pi / 180)) hC5 s5_17
      -- 5.23.14. calculation
      have s5_23_14 : EuclideanGeometry.angle A C B < (90 : ℝ) * Real.pi / 180 := by
        calc EuclideanGeometry.angle A C B = EuclideanGeometry.angle B C A := s3
          _ < (90 : ℝ) * Real.pi / 180 := s5_23_13
      -- 5.23.15. mun:iff-both-true, from 5.23.12, 5.23.14
      exact (Parley.Items.Stdlib.Reasoning.mun_iff_both_true (P := EuclideanGeometry.angle A C B < (90 : ℝ) * Real.pi / 180) (Q := dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2) s5_23_14 s5_23_12)
    · skip
      -- 5.23.16. mun:between-apart R := B, S := C, T := H, from C6
      have s5_23_16a : C ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := B) (S := C) (T := H) hC6)
      have s5_23_16b : H ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := B) (S := C) (T := H) hC6)
      -- 5.23.17. mun:modus-ponens, from 1, 5.23.16
      have s5_23_17 : EuclideanGeometry.angle A H B = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ B) (Q := EuclideanGeometry.angle A H B = (90 : ℝ) * Real.pi / 180) s1e s5_23_16b)
      -- 5.23.18. mun:right-angle-triangle P := A, Q := H, R := B, from H4, 1, 5.23.16, 5.23.17
      have s5_23_18 : LeanBridges.Geometry.Triangle A H B := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := A) (Q := H) (R := B) s1c (Ne.symm s5_23_16b) s5_23_17 hH4.1)
      -- 5.23.19. thm:pythagoras C := H, from 5.23.17, 5.23.18
      have s5_23_19 : dist A B ^ 2 = dist A H ^ 2 + dist B H ^ 2 := by exact (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := A) (B := B) (C := H) (by (have h := s5_23_18; rw [LeanBridges.Geometry.triangle_swap_23 A H B] at h; exact h) : LeanBridges.Geometry.Triangle A B H) s5_23_17)
      -- 5.23.20. mun:segment-addition P := C, Q := H, S := B, from C6
      have s5_23_20 : dist C B + dist B H = dist C H := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := C) (Q := H) (S := B) hC6)
      -- 5.23.21. calculation
      have s5_23_21 : dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2 := by
        calc dist A B ^ 2 = dist A H ^ 2 + dist H B ^ 2 := (by (have h := s5_23_19; rw [dist_comm B H] at h; exact h) : dist A B ^ 2 = dist A H ^ 2 + dist H B ^ 2)
          _ = dist A C ^ 2 - dist H C ^ 2 + dist H B ^ 2 := by linear_combination (-1) * s5_12
          _ = dist A C ^ 2 - dist H C ^ 2 + (dist C H - dist C B) ^ 2 := by
              rw [dist_comm C B] at s5_23_20
              rw [dist_comm H B, dist_comm H C, dist_comm C B]
              exact (by linear_combination (-dist B C + dist B H + dist C H) * s5_23_20)
          _ = dist A C ^ 2 + dist B C ^ 2 - 2 * (dist B C * dist C H) := by
              rw [dist_comm H C, dist_comm C B]
              exact (by ring1)
          _ < dist A C ^ 2 + dist B C ^ 2 := s5_20
      -- 5.23.22. mun:angle-along-segment P := C, Q := H, R := A, S := B, from C6, H4, 1
      have s5_23_22 : EuclideanGeometry.angle B C A = EuclideanGeometry.angle H C A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := C) (Q := H) (R := A) (S := B) hC6 hH4.2.2.1 hH4.1 s1c)
      -- 5.23.23. calculation
      have s5_23_23 : EuclideanGeometry.angle A C B < (90 : ℝ) * Real.pi / 180 := by
        calc EuclideanGeometry.angle A C B = EuclideanGeometry.angle B C A := s3
          _ = EuclideanGeometry.angle H C A := s5_23_22
          _ < (90 : ℝ) * Real.pi / 180 := s5_17
      -- 5.23.24. mun:iff-both-true, from 5.23.21, 5.23.23
      exact (Parley.Items.Stdlib.Reasoning.mun_iff_both_true (P := EuclideanGeometry.angle A C B < (90 : ℝ) * Real.pi / 180) (Q := dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2) s5_23_23 s5_23_21)
    · skip
      -- 5.23.25. mun:between-ends-apart R := C, S := H, T := B, from C7
      have s5_23_25 : H ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := C) (S := H) (T := B) hC7)
      -- 5.23.26. mun:modus-ponens, from 1, 5.23.25
      have s5_23_26 : EuclideanGeometry.angle A H B = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ B) (Q := EuclideanGeometry.angle A H B = (90 : ℝ) * Real.pi / 180) s1e s5_23_25)
      -- 5.23.27. mun:right-angle-triangle P := A, Q := H, R := B, from H4, 1, 5.23.25, 5.23.26
      have s5_23_27 : LeanBridges.Geometry.Triangle A H B := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := A) (Q := H) (R := B) s1c (Ne.symm s5_23_25) s5_23_26 hH4.1)
      -- 5.23.28. thm:pythagoras C := H, from 5.23.26, 5.23.27
      have s5_23_28 : dist A B ^ 2 = dist A H ^ 2 + dist B H ^ 2 := by exact (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := A) (B := B) (C := H) (by (have h := s5_23_27; rw [LeanBridges.Geometry.triangle_swap_23 A H B] at h; exact h) : LeanBridges.Geometry.Triangle A B H) s5_23_26)
      -- 5.23.29. mun:segment-addition P := H, Q := B, S := C, from C7
      have s5_23_29 : dist H C + dist C B = dist H B := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := H) (Q := B) (S := C) hC7)
      -- 5.23.30. calculation
      have s5_23_30 : dist A C ^ 2 + dist B C ^ 2 < dist A B ^ 2 := by
        calc dist A C ^ 2 + dist B C ^ 2 < dist A C ^ 2 + dist B C ^ 2 + 2 * (dist B C * dist C H) := s5_21
          _ = dist A C ^ 2 - dist H C ^ 2 + (dist H C + dist C B) ^ 2 := by
              rw [dist_comm H C, dist_comm C B]
              exact (by ring1)
          _ = dist A C ^ 2 - dist H C ^ 2 + dist H B ^ 2 := congrArg (fun t : ℝ => dist A C ^ 2 - dist H C ^ 2 + t ^ 2) s5_23_29
          _ = dist A H ^ 2 + dist H B ^ 2 := by linear_combination s5_12
          _ = dist A B ^ 2 := (by (have h := s5_23_28.symm; rw [dist_comm B H] at h; exact h) : dist A H ^ 2 + dist H B ^ 2 = dist A B ^ 2)
      -- 5.23.31. inequalities
      have s5_23_31 : dist A C ^ 2 + dist B C ^ 2 ≤ dist A B ^ 2 := by linarith only [s5_23_30]
      -- 5.23.32. inequalities, from 5.23.31
      have s5_23_32 : ¬ dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2 := by linarith only [s5_23_31]
      -- 5.23.33. axi:supplementary-angles A := H, B := C, C := B, D := A, from C7, H4, 1
      have s5_23_33 : EuclideanGeometry.angle H C A + EuclideanGeometry.angle A C B = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := H) (B := C) (C := B) (D := A) hC7 hH4.2.2.1 s1c hH4.1)
      -- 5.23.34. algebra, from 5.23.33
      have s5_23_34 : EuclideanGeometry.angle A C B = (180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle H C A := by linear_combination ((32400) / ((180) * (180))) * s5_23_33
      -- 5.23.35. inequalities
      have s5_23_35 : (90 : ℝ) * Real.pi / 180 < (180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle H C A := by linarith only [s5_17]
      -- 5.23.36. calculation
      have s5_23_36 : EuclideanGeometry.angle A C B > (90 : ℝ) * Real.pi / 180 := by
        calc EuclideanGeometry.angle A C B = (180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle H C A := s5_23_34
          _ > (90 : ℝ) * Real.pi / 180 := s5_23_35
      -- 5.23.37. inequalities
      have s5_23_37 : EuclideanGeometry.angle A C B ≥ (90 : ℝ) * Real.pi / 180 := by linarith only [s5_23_36]
      -- 5.23.38. inequalities, from 5.23.37
      have s5_23_38 : ¬ EuclideanGeometry.angle A C B < (90 : ℝ) * Real.pi / 180 := by linarith only [s5_23_37]
      -- 5.23.39. mun:iff-both-false, from 5.23.32, 5.23.38
      exact (Parley.Items.Stdlib.Reasoning.mun_iff_both_false (P := EuclideanGeometry.angle A C B < (90 : ℝ) * Real.pi / 180) (Q := dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2) s5_23_38 s5_23_32)

end Parley.Proofs.Euclid.AcuteAngleBySquares.AcuteAngleBySquares

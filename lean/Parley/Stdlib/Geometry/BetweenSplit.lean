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
public import Parley.Items.Stdlib.Reasoning
public import Parley.Stdlib.Geometry.OffLineOther
public import Parley.Stdlib.Geometry.OnLineOther
public import Parley.Stdlib.Geometry.PointOffLine

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.BetweenSplit

theorem between_split (A : ℂ) (B : ℂ) (M : ℂ) (P : ℂ) (hH5 : Sbtw ℝ A M B) (hH6 : Sbtw ℝ A P B) :
    ((P = M ∨ Sbtw ℝ A P M) ∨ Sbtw ℝ M P B) := by
  -- 1. mun:between-ends-apart R := M, S := A, T := B, from H5
  have s1 : A ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := M) (S := A) (T := B) hH5)
  -- 2. mun:between-apart R := M, S := A, T := B, from H5
  have s2a : A ≠ M := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := M) (S := A) (T := B) hH5)
  have s2b : B ≠ M := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := M) (S := A) (T := B) hH5)
  -- 3. mun:between-apart R := P, S := A, T := B, from H6
  have s3a : A ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := P) (S := A) (T := B) hH6)
  have s3b : B ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := P) (S := A) (T := B) hH6)
  -- 4. mun:between-collinear R := M, S := A, T := B, from H5
  have s4 : Collinear ℝ {B, M, A} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := M) (S := A) (T := B) hH5)
  -- 5. def:on-line P := M, from 1, 4
  have s5 : M ∈ LeanBridges.Geometry.line A B := ((Parley.Items.Stdlib.Geometry.def_on_line (A := A) (B := B) (P := M) s1)).mpr (by (have h := s4; rw [LeanBridges.Geometry.collinear_rot_312 B M A] at h; exact h) : Collinear ℝ {A, B, M})
  -- 6. mun:between-collinear R := P, S := A, T := B, from H6
  have s6 : Collinear ℝ {B, P, A} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := P) (S := A) (T := B) hH6)
  -- 7. def:on-line, from 1, 6
  have s7 : P ∈ LeanBridges.Geometry.line A B := ((Parley.Items.Stdlib.Geometry.def_on_line (A := A) (B := B) (P := P) s1)).mpr (by (have h := s6; rw [LeanBridges.Geometry.collinear_rot_312 B P A] at h; exact h) : Collinear ℝ {A, B, P})
  -- 8. mun:on-line-ends, from 1
  have s8a : A ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := B) s1)
  have s8b : B ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := A) (B := B) s1)
  -- 9. obtain O: mun:point-off-line, from 1
  obtain ⟨O, s9a, s9b⟩ := (Parley.Stdlib.Geometry.PointOffLine.point_off_line (A := A) (B := B) s1)
  -- 10. mun:on-off-apart X := P, Y := O, from 7, 9
  have s10 : P ≠ O := by exact (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := A) (B := B) (X := P) (Y := O) s7 s9b)
  -- 11. axi:excluded-middle P := P = M
  have s11 : P = M ∨ P ≠ M := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := P = M))
  -- 12. cases, from 11
  rcases s11 with hC1 | hC2
  · skip
    -- 12.1. mun:or-left, from C1
    have s12_1 : P = M ∨ Sbtw ℝ A P M := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := P = M) (Q := Sbtw ℝ A P M) hC1)
    -- 12.2. mun:or-left, from 12.1
    exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := P = M ∨ Sbtw ℝ A P M) (Q := Sbtw ℝ M P B) s12_1)
  · skip
    -- 12.3. mun:off-line-other X := P, Y := A, from 1, 3, 7, 8, 9
    have s12_3 : ¬ O ∈ LeanBridges.Geometry.line P A := by exact (Parley.Stdlib.Geometry.OffLineOther.off_line_other (A := A) (B := B) (X := P) (Y := A) (O := O) s1 (Ne.symm s3a) s7 s8a s9b)
    -- 12.4. mun:off-line-swap R := P, P := A, Q := O, from 3, 12.3
    have s12_4 : ¬ A ∈ LeanBridges.Geometry.line P O := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_swap (P := A) (Q := O) (R := P) (Ne.symm s3a) s12_3)
    -- 12.5. mun:off-line-other X := P, Y := B, from 1, 3, 7, 8, 9
    have s12_5 : ¬ O ∈ LeanBridges.Geometry.line P B := by exact (Parley.Stdlib.Geometry.OffLineOther.off_line_other (A := A) (B := B) (X := P) (Y := B) (O := O) s1 (Ne.symm s3b) s7 s8b s9b)
    -- 12.6. mun:off-line-swap R := P, P := B, Q := O, from 3, 12.5
    have s12_6 : ¬ B ∈ LeanBridges.Geometry.line P O := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_swap (P := B) (Q := O) (R := P) (Ne.symm s3b) s12_5)
    -- 12.7. mun:off-line-other X := P, Y := M, from C2, 1, 5, 7, 9
    have s12_7 : ¬ O ∈ LeanBridges.Geometry.line P M := by exact (Parley.Stdlib.Geometry.OffLineOther.off_line_other (A := A) (B := B) (X := P) (Y := M) (O := O) s1 hC2 s7 s5 s9b)
    -- 12.8. mun:off-line-swap R := P, P := M, Q := O, from C2, 12.7
    have s12_8 : ¬ M ∈ LeanBridges.Geometry.line P O := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_swap (P := M) (Q := O) (R := P) hC2 s12_7)
    -- 12.9. mun:on-line-ends A := P, B := O, from 10
    have s12_9a : P ∈ LeanBridges.Geometry.line P O := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := P) (B := O) s10)
    have s12_9b : O ∈ LeanBridges.Geometry.line P O := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := P) (B := O) s10)
    -- 12.10. mun:segment-across-line A := P, B := O, P := A, Q := B, M := P, from H6, 10, 12.4, 12.9
    have s12_10 : Complex.im ((A - P) / (O - P)) * Complex.im ((B - P) / (O - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := P) (B := O) (M := P) (P := A) (Q := B) s10 s12_9a s12_4 hH6)
    -- 12.11. axi:plane-separation A := P, B := O, P := M, Q := A, from 10, 12.4, 12.8
    have s12_11 : 0 < Complex.im ((M - P) / (O - P)) * Complex.im ((A - P) / (O - P)) ∨ Complex.im ((M - P) / (O - P)) * Complex.im ((A - P) / (O - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.axi_plane_separation (A := P) (B := O) (P := M) (Q := A) s10 s12_8 s12_4)
    -- 12.12. mun:on-line-other X := P, Y := B, Z := M, from 1, 3, 5, 7, 8
    have s12_12 : M ∈ LeanBridges.Geometry.line P B := by exact (Parley.Stdlib.Geometry.OnLineOther.on_line_other (A := A) (B := B) (X := P) (Y := B) (Z := M) s1 (Ne.symm s3b) s7 s8b s5)
    -- 12.13. mun:on-line-other X := P, Y := A, Z := M, from 1, 3, 5, 7, 8
    have s12_13 : M ∈ LeanBridges.Geometry.line P A := by exact (Parley.Stdlib.Geometry.OnLineOther.on_line_other (A := A) (B := B) (X := P) (Y := A) (Z := M) s1 (Ne.symm s3a) s7 s8a s5)
    -- 12.14. cases, from 12.11
    rcases s12_11 with hC3 | hC9
    · skip
      -- 12.14.1. mun:same-opposite-opposite A := P, B := O, P := M, Q := A, R := B, from C3, 12.10
      have s12_14_1 : Complex.im ((M - P) / (O - P)) * Complex.im ((B - P) / (O - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := P) (B := O) (P := M) (Q := A) (R := B) hC3 s12_10)
      -- 12.14.2. mun:on-line-cases P := M, Q := P, R := B, from 3, 12.12
      have s12_14_2 : (((M = P ∨ Sbtw ℝ P M B) ∨ M = B) ∨ Sbtw ℝ P B M) ∨ Sbtw ℝ M P B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := M) (Q := P) (R := B) (Ne.symm s3b) s12_12)
      -- 12.14.3. cases, from 12.14.2
      have s12_14_3 : Sbtw ℝ M P B := by
        rcases s12_14_2 with (((hC4 | hC5) | hC6) | hC7) | hC8
        · skip
          -- 12.14.3.1. restate C2
          have s12_14_3_1 : P ≠ M := by exact hC2
          exact absurd hC4.symm s12_14_3_1
        · skip
          -- 12.14.3.2. mun:segment-off-line A := P, B := O, P := B, Q := P, X := M, from C5, 10, 12.6, 12.9
          have s12_14_3_2 : 0 < Complex.im ((M - P) / (O - P)) * Complex.im ((B - P) / (O - P)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := P) (B := O) (P := B) (Q := P) (X := M) s10 s12_9a s12_6 (by (have h := hC5; rw [sbtw_comm (x := P) (y := M) (z := B)] at h; exact h) : Sbtw ℝ B M P))
          -- 12.14.3.3. mun:same-not-opposite A := P, B := O, P := M, Q := B, from 12.14.3.2
          have s12_14_3_3 : ¬ Complex.im ((M - P) / (O - P)) * Complex.im ((B - P) / (O - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_not_opposite (A := P) (B := O) (P := M) (Q := B) s12_14_3_2)
          -- 12.14.3.4. restate 12.14.1
          have s12_14_3_4 : Complex.im ((M - P) / (O - P)) * Complex.im ((B - P) / (O - P)) < 0 := by exact s12_14_1
          exact absurd s12_14_3_4 s12_14_3_3
        · skip
          -- 12.14.3.5. restate 2
          have s12_14_3_5 : B ≠ M := by exact s2b
          exact absurd hC6.symm s12_14_3_5
        · skip
          -- 12.14.3.6. mun:segment-beyond-off-line A := P, B := O, P := M, Q := P, X := B, from C7, 10, 12.6, 12.9
          have s12_14_3_6 : 0 < Complex.im ((M - P) / (O - P)) * Complex.im ((B - P) / (O - P)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_beyond_off_line (A := P) (B := O) (P := M) (Q := P) (X := B) s10 s12_9a s12_6 (by (have h := hC7; rw [sbtw_comm (x := P) (y := B) (z := M)] at h; exact h) : Sbtw ℝ M B P))
          -- 12.14.3.7. mun:same-not-opposite A := P, B := O, P := M, Q := B, from 12.14.3.6
          have s12_14_3_7 : ¬ Complex.im ((M - P) / (O - P)) * Complex.im ((B - P) / (O - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_not_opposite (A := P) (B := O) (P := M) (Q := B) s12_14_3_6)
          -- 12.14.3.8. restate 12.14.1
          have s12_14_3_8 : Complex.im ((M - P) / (O - P)) * Complex.im ((B - P) / (O - P)) < 0 := by exact s12_14_1
          exact absurd s12_14_3_8 s12_14_3_7
        · skip
          exact hC8
      -- 12.14.4. mun:or-right, from 12.14.3
      exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := P = M ∨ Sbtw ℝ A P M) (Q := Sbtw ℝ M P B) s12_14_3)
    · skip
      -- 12.14.5. mun:on-line-cases P := M, Q := P, R := A, from 3, 12.13
      have s12_14_5 : (((M = P ∨ Sbtw ℝ P M A) ∨ M = A) ∨ Sbtw ℝ P A M) ∨ Sbtw ℝ M P A := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := M) (Q := P) (R := A) (Ne.symm s3a) s12_13)
      -- 12.14.6. cases, from 12.14.5
      have s12_14_6 : Sbtw ℝ M P A := by
        rcases s12_14_5 with (((hC10 | hC11) | hC12) | hC13) | hC14
        · skip
          -- 12.14.6.1. restate C2
          have s12_14_6_1 : P ≠ M := by exact hC2
          exact absurd hC10.symm s12_14_6_1
        · skip
          -- 12.14.6.2. mun:segment-off-line A := P, B := O, P := A, Q := P, X := M, from C11, 10, 12.4, 12.9
          have s12_14_6_2 : 0 < Complex.im ((M - P) / (O - P)) * Complex.im ((A - P) / (O - P)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := P) (B := O) (P := A) (Q := P) (X := M) s10 s12_9a s12_4 (by (have h := hC11; rw [sbtw_comm (x := P) (y := M) (z := A)] at h; exact h) : Sbtw ℝ A M P))
          -- 12.14.6.3. mun:same-not-opposite A := P, B := O, P := M, Q := A, from 12.14.6.2
          have s12_14_6_3 : ¬ Complex.im ((M - P) / (O - P)) * Complex.im ((A - P) / (O - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_not_opposite (A := P) (B := O) (P := M) (Q := A) s12_14_6_2)
          -- 12.14.6.4. restate C9
          have s12_14_6_4 : Complex.im ((M - P) / (O - P)) * Complex.im ((A - P) / (O - P)) < 0 := by exact hC9
          exact absurd s12_14_6_4 s12_14_6_3
        · skip
          -- 12.14.6.5. restate 2
          have s12_14_6_5 : A ≠ M := by exact s2a
          exact absurd hC12.symm s12_14_6_5
        · skip
          -- 12.14.6.6. mun:segment-beyond-off-line A := P, B := O, P := M, Q := P, X := A, from C13, 10, 12.4, 12.9
          have s12_14_6_6 : 0 < Complex.im ((M - P) / (O - P)) * Complex.im ((A - P) / (O - P)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_beyond_off_line (A := P) (B := O) (P := M) (Q := P) (X := A) s10 s12_9a s12_4 (by (have h := hC13; rw [sbtw_comm (x := P) (y := A) (z := M)] at h; exact h) : Sbtw ℝ M A P))
          -- 12.14.6.7. mun:same-not-opposite A := P, B := O, P := M, Q := A, from 12.14.6.6
          have s12_14_6_7 : ¬ Complex.im ((M - P) / (O - P)) * Complex.im ((A - P) / (O - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_not_opposite (A := P) (B := O) (P := M) (Q := A) s12_14_6_6)
          -- 12.14.6.8. restate C9
          have s12_14_6_8 : Complex.im ((M - P) / (O - P)) * Complex.im ((A - P) / (O - P)) < 0 := by exact hC9
          exact absurd s12_14_6_8 s12_14_6_7
        · skip
          exact hC14
      -- 12.14.7. mun:or-right, from 12.14.6
      have s12_14_7 : P = M ∨ Sbtw ℝ A P M := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := P = M) (Q := Sbtw ℝ A P M) (by (have h := s12_14_6; rw [sbtw_comm (x := M) (y := P) (z := A)] at h; exact h) : Sbtw ℝ A P M))
      -- 12.14.8. mun:or-left, from 12.14.7
      exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := P = M ∨ Sbtw ℝ A P M) (Q := Sbtw ℝ M P B) s12_14_7)

end Parley.Stdlib.Geometry.BetweenSplit

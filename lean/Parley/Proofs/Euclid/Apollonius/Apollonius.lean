module

public import Geometry
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
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
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
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
public import Parley.Stdlib.Geometry.Foot
public import Parley.Stdlib.Geometry.OffLineOther
public import Parley.Stdlib.Geometry.OnLineOther
public import Parley.Stdlib.Geometry.RightAngleAlong

/-! Written from proofs/euclid/apollonius.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.Apollonius.Apollonius

theorem apollonius (A : ℂ) (B : ℂ) (C : ℂ) (M : ℂ) (hH5 : Sbtw ℝ B M C) (hH6 : dist B M = dist M C) :
    dist A B ^ 2 + dist A C ^ 2 = 2 * dist A M ^ 2 + 2 * dist B M ^ 2 := by
  -- 1. mun:between-ends-apart R := M, S := B, T := C, from H5
  have s1 : B ≠ C := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := M) (S := B) (T := C) hH5)
  -- 2. mun:on-line-ends A := B, B := C, from 1
  have s2a : B ∈ LeanBridges.Geometry.line B C := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := B) (B := C) s1)
  have s2b : C ∈ LeanBridges.Geometry.line B C := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := B) (B := C) s1)
  -- 3. mun:between-collinear R := M, S := B, T := C, from H5
  have s3 : Collinear ℝ {C, M, B} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := M) (S := B) (T := C) hH5)
  -- 4. def:on-line P := M, A := B, B := C, from 1, 3
  have s4 : M ∈ LeanBridges.Geometry.line B C := ((Parley.Items.Stdlib.Geometry.def_on_line (A := B) (B := C) (P := M) s1)).mpr (by (have h := s3; rw [LeanBridges.Geometry.collinear_rot_312 C M B] at h; exact h) : Collinear ℝ {B, C, M})
  -- 5. def:line P := B, A := B, B := C, from 1, 2
  have s5 : B ∈ LeanBridges.Geometry.line B C := ((Parley.Items.Stdlib.Geometry.def_line (P := B) (A := B) (B := C) s1)).mpr s2a
  -- 6. def:line P := C, A := B, B := C, from 1, 2
  have s6 : C ∈ LeanBridges.Geometry.line B C := ((Parley.Items.Stdlib.Geometry.def_line (P := C) (A := B) (B := C) s1)).mpr s2b
  -- 7. def:line P := M, A := B, B := C, from 1, 4
  have s7 : M ∈ LeanBridges.Geometry.line B C := ((Parley.Items.Stdlib.Geometry.def_line (P := M) (A := B) (B := C) s1)).mpr s4
  -- 8. obtain f: axi:ruler A := B, B := C, from 1
  obtain ⟨f, s8a, ⟨s8b, s8c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_ruler (A := B) (B := C) s1)
  -- 9. instantiate P := B, Q := M in line 8, from 5, 7
  have s9 : dist B M = abs (f B - f M) := by exact (s8c B s5 M s7)
  -- 10. instantiate P := M, Q := C in line 8, from 6, 7
  have s10 : dist M C = abs (f M - f C) := by exact (s8c M s7 C s6)
  -- 11. instantiate P := B, Q := C in line 8, from 5, 6
  have s11 : dist B C = abs (f B - f C) := by exact (s8c B s5 C s6)
  -- 12. calculation
  have s12 : dist B M ^ 2 = (f B - f M) ^ 2 := by
    calc dist B M ^ 2 = abs (f B - f M) ^ 2 := congrArg (fun t : ℝ => t ^ 2) s9
      _ = (f B - f M) ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_abs_square (x := f B - f M))
  -- 13. calculation
  have s13 : dist M C ^ 2 = (f M - f C) ^ 2 := by
    calc dist M C ^ 2 = abs (f M - f C) ^ 2 := congrArg (fun t : ℝ => t ^ 2) s10
      _ = (f M - f C) ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_abs_square (x := f M - f C))
  -- 14. calculation
  have s14 : dist B C ^ 2 = (f B - f C) ^ 2 := by
    calc dist B C ^ 2 = abs (f B - f C) ^ 2 := congrArg (fun t : ℝ => t ^ 2) s11
      _ = (f B - f C) ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_abs_square (x := f B - f C))
  -- 15. calculation
  have s15 : dist B C = 2 * dist B M := by
    calc dist B C = dist B M + dist M C := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := B) (Q := C) (S := M) hH5).symm
      _ = dist B M + dist B M := congrArg (fun t : ℝ => dist B M + t) hH6.symm
      _ = 2 * dist B M := by ring1
  -- 16. calculation
  have s16 : (f B - 2 * f M + f C) ^ 2 = 0 := by
    calc (f B - 2 * f M + f C) ^ 2 = 2 * (f B - f M) ^ 2 + 2 * (f M - f C) ^ 2 - (f B - f C) ^ 2 := by ring1
      _ = 2 * dist B M ^ 2 + 2 * (f M - f C) ^ 2 - (f B - f C) ^ 2 := congrArg (fun t : ℝ => 2 * t + 2 * (f M - f C) ^ 2 - (f B - f C) ^ 2) s12.symm
      _ = 2 * dist B M ^ 2 + 2 * dist M C ^ 2 - (f B - f C) ^ 2 := congrArg (fun t : ℝ => 2 * dist B M ^ 2 + 2 * t - (f B - f C) ^ 2) s13.symm
      _ = 2 * dist B M ^ 2 + 2 * dist M C ^ 2 - dist B C ^ 2 := congrArg (fun t : ℝ => 2 * dist B M ^ 2 + 2 * dist M C ^ 2 - t) s14.symm
      _ = 2 * dist B M ^ 2 + 2 * dist B M ^ 2 - dist B C ^ 2 := congrArg (fun t : ℝ => 2 * dist B M ^ 2 + 2 * t ^ 2 - dist B C ^ 2) hH6.symm
      _ = 2 * dist B M ^ 2 + 2 * dist B M ^ 2 - (2 * dist B M) ^ 2 := congrArg (fun t : ℝ => 2 * dist B M ^ 2 + 2 * dist B M ^ 2 - t ^ 2) s15
      _ = 0 := by ring1
  -- 17. mun:square-zero x := f(B) − 2·f(M) + f(C), from 5, 6, 7, 8, 16
  have s17 : f B - 2 * f M + f C = 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_zero (x := f B - 2 * f M + f C) s16)
  -- 18. proof
  have s18 : ∀ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line B C → dist X B ^ 2 + dist X C ^ 2 = 2 * dist X M ^ 2 + 2 * dist B M ^ 2 := by
    intro X hK1
    intro hA1
    -- 18.1. def:line P := X, A := B, B := C, from A1, 1
    have s18_1 : X ∈ LeanBridges.Geometry.line B C := ((Parley.Items.Stdlib.Geometry.def_line (P := X) (A := B) (B := C) s1)).mpr hA1
    -- 18.2. instantiate P := X, Q := B in line 8, from 5, 18.1
    have s18_2 : dist X B = abs (f X - f B) := by exact (s8c X s18_1 B s5)
    -- 18.3. instantiate P := X, Q := C in line 8, from 6, 18.1
    have s18_3 : dist X C = abs (f X - f C) := by exact (s8c X s18_1 C s6)
    -- 18.4. instantiate P := X, Q := M in line 8, from 7, 18.1
    have s18_4 : dist X M = abs (f X - f M) := by exact (s8c X s18_1 M s7)
    -- 18.5. calculation
    have s18_5 : dist X B ^ 2 = (f X - f B) ^ 2 := by
      calc dist X B ^ 2 = abs (f X - f B) ^ 2 := congrArg (fun t : ℝ => t ^ 2) s18_2
        _ = (f X - f B) ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_abs_square (x := f X - f B))
    -- 18.6. calculation
    have s18_6 : dist X C ^ 2 = (f X - f C) ^ 2 := by
      calc dist X C ^ 2 = abs (f X - f C) ^ 2 := congrArg (fun t : ℝ => t ^ 2) s18_3
        _ = (f X - f C) ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_abs_square (x := f X - f C))
    -- 18.7. calculation
    have s18_7 : dist X M ^ 2 = (f X - f M) ^ 2 := by
      calc dist X M ^ 2 = abs (f X - f M) ^ 2 := congrArg (fun t : ℝ => t ^ 2) s18_4
        _ = (f X - f M) ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_abs_square (x := f X - f M))
    -- 18.8. calculation
    calc dist X B ^ 2 + dist X C ^ 2 = (f X - f B) ^ 2 + dist X C ^ 2 := congrArg (fun t : ℝ => t + dist X C ^ 2) s18_5
      _ = (f X - f B) ^ 2 + (f X - f C) ^ 2 := congrArg (fun t : ℝ => (f X - f B) ^ 2 + t) s18_6
      _ = 2 * (f X - f M) ^ 2 + 2 * (f B - f M) ^ 2 := by linear_combination (-f B + f C + 2 * f M - 2 * f X) * s17
      _ = 2 * dist X M ^ 2 + 2 * (f B - f M) ^ 2 := congrArg (fun t : ℝ => 2 * t + 2 * (f B - f M) ^ 2) s18_7.symm
      _ = 2 * dist X M ^ 2 + 2 * dist B M ^ 2 := congrArg (fun t : ℝ => 2 * dist X M ^ 2 + 2 * t) s12.symm
  -- 19. axi:excluded-middle P := A is on line BC
  have s19 : A ∈ LeanBridges.Geometry.line B C ∨ ¬ A ∈ LeanBridges.Geometry.line B C := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := A ∈ LeanBridges.Geometry.line B C))
  -- 20. cases, from 19
  rcases s19 with hC1 | hC2
  · skip
    -- 20.1. instantiate X := A in line 18, from C1
    exact (s18 A (Set.mem_univ _) hC1)
  · skip
    -- 20.2. mun:triangle-off-line P := A, Q := B, R := C, from C2, 1
    have s20_2 : LeanBridges.Geometry.Triangle A B C := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := A) (Q := B) (R := C) s1 hC2)
    -- 20.3. obtain H, S: mun:foot P := A, Q := B, R := C, from 20.2
    obtain ⟨H, s20_3a, S, s20_3b, ⟨⟨⟨⟨⟨s20_3c, s20_3d⟩, s20_3e⟩, s20_3f⟩, s20_3g⟩, s20_3h⟩⟩ := (Parley.Stdlib.Geometry.Foot.foot (P := A) (Q := B) (R := C) s20_2)
    -- 20.4. proof
    have s20_4 : ∀ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line B C → dist A X ^ 2 = dist A H ^ 2 + dist H X ^ 2 := by
      intro X hK2
      intro hA2
      -- 20.4.1. axi:excluded-middle P := X = H
      have s20_4_1 : X = H ∨ X ≠ H := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := X = H))
      -- 20.4.2. cases, from 20.4.1
      rcases s20_4_1 with hC3 | hC4
      · skip
        -- 20.4.2.1. mun:distance-zero P := H, Q := X, from C3
        have s20_4_2_1 : dist H X = 0 := ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := H) (Q := X))).mpr hC3.symm
        -- 20.4.2.2. calculation
        calc dist A X ^ 2 = dist A H ^ 2 := by (have h := congrArg (fun t : ℂ => (dist A t : ℂ) ^ 2) hC3; push_cast at h ⊢; exact_mod_cast h)
          _ = dist A H ^ 2 + dist H X ^ 2 := by linear_combination (-dist H X) * s20_4_2_1
      · skip
        -- 20.4.2.3. mun:on-line-other A := B, B := C, X := H, Y := S, Z := X, from A2, 1, 20.3
        have s20_4_2_3 : X ∈ LeanBridges.Geometry.line H S := by exact (Parley.Stdlib.Geometry.OnLineOther.on_line_other (A := B) (B := C) (X := H) (Y := S) (Z := X) s1 (Ne.symm s20_3e) s20_3c s20_3d hA2)
        -- 20.4.2.4. mun:off-line-other A := B, B := C, X := H, Y := X, O := A, from A2, C2, C4, 1, 20.3
        have s20_4_2_4 : ¬ A ∈ LeanBridges.Geometry.line H X := by exact (Parley.Stdlib.Geometry.OffLineOther.off_line_other (A := B) (B := C) (X := H) (Y := X) (O := A) s1 (Ne.symm hC4) s20_3c hA2 hC2)
        -- 20.4.2.5. mun:triangle-off-line P := A, Q := H, R := X, from C4, 20.4.2.4
        have s20_4_2_5 : LeanBridges.Geometry.Triangle A H X := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := A) (Q := H) (R := X) (Ne.symm hC4) s20_4_2_4)
        -- 20.4.2.6. mun:right-angle-along P := A, T := X, from 20.3, 20.4.2.3, 20.4.2.5
        have s20_4_2_6 : EuclideanGeometry.angle A H X = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Stdlib.Geometry.RightAngleAlong.right_angle_along (P := A) (H := H) (S := S) (T := X) s20_3f s20_3e s20_3h s20_4_2_3 (Ne.symm s20_4_2_5.2.1) s20_3g s20_4_2_5)
        -- 20.4.2.7. thm:pythagoras B := X, C := H, from 20.4.2.5, 20.4.2.6
        have s20_4_2_7 : dist A X ^ 2 = dist A H ^ 2 + dist X H ^ 2 := by exact (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := A) (B := X) (C := H) (by (have h := s20_4_2_5; rw [LeanBridges.Geometry.triangle_swap_23 A H X] at h; exact h) : LeanBridges.Geometry.Triangle A X H) s20_4_2_6)
        exact (by (have h := s20_4_2_7; rw [dist_comm X H] at h; exact h) : dist A X ^ 2 = dist A H ^ 2 + dist H X ^ 2)
    -- 20.5. instantiate X := B in line 20.4, from 2
    have s20_5 : dist A B ^ 2 = dist A H ^ 2 + dist H B ^ 2 := by exact (s20_4 B (Set.mem_univ _) s2a)
    -- 20.6. instantiate X := C in line 20.4, from 2
    have s20_6 : dist A C ^ 2 = dist A H ^ 2 + dist H C ^ 2 := by exact (s20_4 C (Set.mem_univ _) s2b)
    -- 20.7. instantiate X := M in line 20.4, from 4
    have s20_7 : dist A M ^ 2 = dist A H ^ 2 + dist H M ^ 2 := by exact (s20_4 M (Set.mem_univ _) s4)
    -- 20.8. instantiate X := H in line 18, from 20.3
    have s20_8 : dist H B ^ 2 + dist H C ^ 2 = 2 * dist H M ^ 2 + 2 * dist B M ^ 2 := by exact (s18 H (Set.mem_univ _) s20_3c)
    -- 20.9. calculation
    calc dist A B ^ 2 + dist A C ^ 2 = 2 * dist A H ^ 2 + dist H B ^ 2 + dist H C ^ 2 := by linear_combination s20_5 + s20_6
      _ = 2 * dist A H ^ 2 + 2 * dist H M ^ 2 + 2 * dist B M ^ 2 := by linear_combination s20_8
      _ = 2 * dist A M ^ 2 + 2 * dist B M ^ 2 := by linear_combination (-2) * s20_7

end Parley.Proofs.Euclid.Apollonius.Apollonius

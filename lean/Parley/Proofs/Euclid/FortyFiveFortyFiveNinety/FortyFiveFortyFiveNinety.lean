module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.AngleSum.AngleSum
public import Parley.Proofs.Wiedijk.Isosceles.Isosceles
public import Parley.Proofs.Wiedijk.Pythagoras.Pythagoras

/-! Written from proofs/euclid/forty-five-forty-five-ninety.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.FortyFiveFortyFiveNinety.FortyFiveFortyFiveNinety

theorem forty_five_forty_five_ninety (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180) (hH6 : dist C A = dist C B) :
    dist A B = Real.sqrt (2 : ℝ) * dist C A ∧ EuclideanGeometry.angle C A B = (45 : ℝ) * Real.pi / 180 := by
  -- 1. thm:pythagoras, from H4, H5
  have s1 : dist A B ^ 2 = dist A C ^ 2 + dist B C ^ 2 := by exact (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := A) (B := B) (C := C) hH4 hH5)
  -- 2. substitute |CB| = |CA| (H6) into line 1
  have s2 : dist A B ^ 2 = dist C A ^ 2 + dist C A ^ 2 := by (have h := (by (have h := Eq.subst (motive := (fun t : ℝ => dist A B ^ 2 = dist A C ^ 2 + t ^ 2)) hH6.symm (by (have h := s1; rw [dist_comm B C] at h; exact h) : dist A B ^ 2 = dist A C ^ 2 + dist C B ^ 2); rw [dist_comm A C] at h; exact h) : dist A B ^ 2 = dist C A ^ 2 + dist C A ^ 2); push_cast at h ⊢; exact_mod_cast h)
  -- 3. calculation
  have s3 : dist A B ^ 2 = (Real.sqrt (2 : ℝ) * dist C A) ^ 2 := by
    calc dist A B ^ 2 = 2 * dist C A ^ 2 := by linear_combination s2
      _ = Real.sqrt (2 : ℝ) ^ 2 * dist C A ^ 2 := by
          have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
          linear_combination (-(dist C A ^ 2)) * hr2
      _ = (Real.sqrt (2 : ℝ) * dist C A) ^ 2 := by ring1
  -- 4. mun:distance-nonneg P := A, Q := B
  have s4 : dist A B ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := A) (Q := B))
  -- 5. mun:distance-nonneg P := C, Q := A
  have s5 : dist C A ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := C) (Q := A))
  -- 6. mun:product-nonneg x := √2, y := |CA|, from 5
  have r40_1 : Real.sqrt (2 : ℝ) ≥ 0 := by
    have hf1 : (11 / 8 : ℝ) < Real.sqrt (2 : ℝ) := (Real.lt_sqrt (show (0 : ℝ) ≤ (11 / 8 : ℝ) by norm_num)).mpr (show (11 / 8 : ℝ) ^ 2 < 2 by norm_num)
    have hf2 : Real.sqrt (2 : ℝ) < (23 / 16 : ℝ) := (Real.sqrt_lt' (show (0 : ℝ) < (23 / 16 : ℝ) by norm_num)).mpr (show 2 < (23 / 16 : ℝ) ^ 2 by norm_num)
    linarith only [hf1, hf2]
  have s6 : Real.sqrt (2 : ℝ) * dist C A ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sqrt (2 : ℝ)) (y := dist C A) r40_1 s5)
  -- 7. mun:square-equal x := |AB|, y := √2·|CA|, from 3, 4, 6
  have s7 : dist A B = Real.sqrt (2 : ℝ) * dist C A := by exact ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := dist A B) (y := Real.sqrt (2 : ℝ) * dist C A) s4 s6)).mp s3
  -- 8. thm:isosceles, from H4, H6
  have s8 : EuclideanGeometry.angle C A B = EuclideanGeometry.angle C B A := by exact (Parley.Proofs.Wiedijk.Isosceles.Isosceles.isosceles (A := A) (B := B) (C := C) hH4 hH6)
  -- 9. thm:angle-sum B := C, C := B, from H4
  have s9 : EuclideanGeometry.angle C A B + EuclideanGeometry.angle A C B + EuclideanGeometry.angle C B A = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Proofs.Wiedijk.AngleSum.AngleSum.angle_sum (A := A) (B := C) (C := B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B))
  -- 10. algebra, from H5, 8, 9
  have s10 : EuclideanGeometry.angle C A B = (45 : ℝ) * Real.pi / 180 := by linear_combination ((-16200) / ((180) * (180))) * hH5 + ((90) / ((180))) * s8 + ((16200) / ((180) * (180))) * s9
  -- 11. join 7, 10
  have s11a : dist A B = Real.sqrt (2 : ℝ) * dist C A := s7
  have s11b : EuclideanGeometry.angle C A B = (45 : ℝ) * Real.pi / 180 := s10
  exact ⟨s11a, s11b⟩

end Parley.Proofs.Euclid.FortyFiveFortyFiveNinety.FortyFiveFortyFiveNinety

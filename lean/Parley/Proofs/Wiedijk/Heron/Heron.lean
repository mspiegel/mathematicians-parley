module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/wiedijk/heron.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Heron.Heron

theorem heron (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) :
    1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C)))) = Real.sqrt ((dist B C + dist C A + dist A B) / 2 * ((dist B C + dist C A + dist A B) / 2 - dist B C) * ((dist B C + dist C A + dist A B) / 2 - dist C A) * ((dist B C + dist C A + dist A B) / 2 - dist A B)) := by
  set s : ℝ := (dist B C + dist C A + dist A B) / 2 with hD1
  -- 1. thm:area-by-sine P := A, Q := B, R := C, from H4
  have s1 : 1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C)))) = 1 / 2 * (dist B C * dist A C) * Real.sin (EuclideanGeometry.angle B C A) := by exact (Parley.Items.Stdlib.Geometry.thm_area_by_sine (P := A) (Q := B) (R := C) hH4.2.2.1 hH4.2.1 (Ne.symm hH4.1))
  -- 2. thm:law-of-cosines P := B, Q := C, R := A, from H4
  have s2 : dist A B ^ 2 = dist B C ^ 2 + dist C A ^ 2 - 2 * (dist B C * dist C A * Real.cos (EuclideanGeometry.angle B C A)) := by exact (Parley.Items.Stdlib.Geometry.thm_law_of_cosines (P := B) (Q := C) (R := A) hH4.2.1 hH4.2.2.1 (Ne.symm hH4.1))
  -- 3. algebra, from 2
  have s3 : 2 * (dist B C * dist A C * Real.cos (EuclideanGeometry.angle B C A)) = dist B C ^ 2 + dist A C ^ 2 - dist A B ^ 2 := by
    rw [dist_comm C A] at s2
    rw [dist_comm C A] at hD1
    exact (by linear_combination s2)
  -- 4. mun:sin-cos-squares a := ∠BCA
  have s4 : Real.sin (EuclideanGeometry.angle B C A) ^ 2 + Real.cos (EuclideanGeometry.angle B C A) ^ 2 = 1 := by
    have hI : Real.sin (EuclideanGeometry.angle B C A) ^ 2 + Real.cos (EuclideanGeometry.angle B C A) ^ 2 = 1 := by exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (EuclideanGeometry.angle B C A : ℂ))))
    exact hI
  -- 5. algebra, from 4
  have s5 : Real.sin (EuclideanGeometry.angle B C A) ^ 2 = 1 - Real.cos (EuclideanGeometry.angle B C A) ^ 2 := by linear_combination s4
  -- 6. calculation
  have s6 : (1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C))))) ^ 2 = s * (s - dist B C) * (s - dist C A) * (s - dist A B) := by
    calc (1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C))))) ^ 2 = (1 / 2 * (dist B C * dist A C) * Real.sin (EuclideanGeometry.angle B C A)) ^ 2 := congrArg (fun t : ℝ => t ^ 2) s1
      _ = (dist B C * dist A C) ^ 2 * Real.sin (EuclideanGeometry.angle B C A) ^ 2 / 4 := by ring1
      _ = (dist B C * dist A C) ^ 2 * (1 - Real.cos (EuclideanGeometry.angle B C A) ^ 2) / 4 := congrArg (fun t : ℝ => (dist B C * dist A C) ^ 2 * t / 4) s5
      _ = (4 * (dist B C * dist A C) ^ 2 - (2 * (dist B C * dist A C * Real.cos (EuclideanGeometry.angle B C A))) ^ 2) / 16 := by ring1
      _ = (4 * (dist B C * dist A C) ^ 2 - (dist B C ^ 2 + dist A C ^ 2 - dist A B ^ 2) ^ 2) / 16 := congrArg (fun t : ℝ => (4 * (dist B C * dist A C) ^ 2 - t ^ 2) / 16) s3
      _ = s * (s - dist B C) * (s - dist C A) * (s - dist A B) := by
          rw [dist_comm C A] at hD1
          rw [dist_comm C A]
          exact (by
            simp only [hD1] at ⊢
            ring1)
  -- 7. mun:area-real P := A, Q := B, R := C, from H4
  -- 8. axi:area-positive P := A, Q := B, R := C, from H4
  have s8 : 1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C)))) > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_area_positive (P := A) (Q := B) (R := C) hH4)
  -- 9. mun:square-nonneg x := the area of △ABC, from 7
  have s9 : (1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C))))) ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := 1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C))))))
  -- 10. substitute (the area of △ABC)² = s·(s − |BC|)·(s − |CA|)·(s − |AB|) (line 6) into line 9
  have s10 : s * (s - dist B C) * (s - dist C A) * (s - dist A B) ≥ 0 := Eq.subst (motive := (fun t : ℝ => t ≥ 0)) s6 s9
  -- 11. def:sqrt x := s·(s − |BC|)·(s − |CA|)·(s − |AB|), from 10
  have s11a : Real.sqrt (s * (s - dist B C) * (s - dist C A) * (s - dist A B)) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := s * (s - dist B C) * (s - dist C A) * (s - dist A B)) s10)
  have s11b : Real.sqrt (s * (s - dist B C) * (s - dist C A) * (s - dist A B)) ^ 2 = s * (s - dist B C) * (s - dist C A) * (s - dist A B) := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := s * (s - dist B C) * (s - dist C A) * (s - dist A B)) s10)
  -- 12. calculation
  have s12 : (1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C))))) ^ 2 = Real.sqrt (s * (s - dist B C) * (s - dist C A) * (s - dist A B)) ^ 2 := by
    calc (1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C))))) ^ 2 = s * (s - dist B C) * (s - dist C A) * (s - dist A B) := s6
      _ = Real.sqrt (s * (s - dist B C) * (s - dist C A) * (s - dist A B)) ^ 2 := s11b.symm
  -- 13. mun:square-equal x := the area of △ABC, y := √(s·(s − |BC|)·(s − |CA|)·(s − |AB|)), from 11, 12
  have r73_2 : 1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C)))) ≥ 0 := by linarith only [s8]
  exact ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := 1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C))))) (y := Real.sqrt (s * (s - dist B C) * (s - dist C A) * (s - dist A B))) r73_2 s11a)).mp s12

end Parley.Proofs.Wiedijk.Heron.Heron

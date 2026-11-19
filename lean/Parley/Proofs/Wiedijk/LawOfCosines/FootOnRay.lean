module

public import Geometry
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
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

/-! Written from proofs/wiedijk/law-of-cosines.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LawOfCosines.FootOnRay

theorem foot_on_ray (P : ℂ) (Q : ℂ) (R : ℂ) (H : ℂ) (hH5 : LeanBridges.Geometry.Triangle P Q R) (hH6 : P ≠ H) (hH7 : Q ≠ H) (hH8 : EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180) (hH9 : EuclideanGeometry.angle H Q P = EuclideanGeometry.angle R Q P) (hH10 : dist H R ^ 2 = (dist Q R - dist Q H) ^ 2) :
    dist H R ^ 2 = dist H Q ^ 2 + dist Q R ^ 2 - 2 * (dist P Q * dist Q R * Real.cos (EuclideanGeometry.angle P Q R)) := by
  -- 1. mun:cosine-right-triangle R := H, from H5, H6, H7, H8
  have s1 : dist Q H = dist Q P * Real.cos (EuclideanGeometry.angle H Q P) := by exact (Parley.Items.Stdlib.Geometry.mun_cosine_right_triangle (P := P) (Q := Q) (R := H) hH6 hH7 hH8 hH5.1)
  -- 2. calculation
  have s2 : EuclideanGeometry.angle H Q P = EuclideanGeometry.angle P Q R := by
    calc EuclideanGeometry.angle H Q P = EuclideanGeometry.angle R Q P := hH9
      _ = EuclideanGeometry.angle P Q R := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := R) (Q := Q) (R := P) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_13 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R Q P))
  -- 3. substitute ∠HQP = ∠PQR (line 2) into line 1
  have s3 : dist Q H = dist Q P * Real.cos (EuclideanGeometry.angle P Q R) := Eq.subst (motive := (fun t : ℝ => dist Q H = dist Q P * Real.cos t)) s2 s1
  -- 4. algebra, from H10
  have s4 : dist H R ^ 2 = dist H Q ^ 2 + dist Q R ^ 2 - 2 * (dist Q R * dist Q H) := by
    rw [dist_comm Q H] at hH10
    rw [dist_comm Q H]
    exact (by linear_combination hH10)
  -- 5. substitute |QH| = |QP|·cos(∠PQR) (line 3) into line 4
  have s5 : dist H R ^ 2 = dist H Q ^ 2 + dist Q R ^ 2 - 2 * (dist Q R * (dist Q P * Real.cos (EuclideanGeometry.angle P Q R))) := Eq.subst (motive := (fun t : ℝ => dist H R ^ 2 = dist H Q ^ 2 + dist Q R ^ 2 - 2 * (dist Q R * t))) s3 s4
  -- 6. algebra, from 5
  rw [dist_comm Q P] at s5
  exact (by linear_combination s5)

end Parley.Proofs.Wiedijk.LawOfCosines.FootOnRay

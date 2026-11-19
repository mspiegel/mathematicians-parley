module

public import Geometry
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
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
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Proofs.Wiedijk.LawOfCosines.DistanceFromFoot
public import Parley.Proofs.Wiedijk.LawOfCosines.PythagorasAtFoot
public import Parley.Stdlib.Geometry.PerpendicularFoot

/-! Written from proofs/wiedijk/law-of-cosines.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LawOfCosines.LawOfCosines

theorem law_of_cosines (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) :
    dist R P ^ 2 = dist P Q ^ 2 + dist Q R ^ 2 - 2 * (dist P Q * dist Q R * Real.cos (EuclideanGeometry.angle P Q R)) := by
  -- 1. obtain H: thm:perpendicular-foot, from H4
  obtain ⟨H, s1a, ⟨⟨⟨s1b, s1c⟩, s1d⟩, s1e⟩⟩ := (Parley.Stdlib.Geometry.PerpendicularFoot.perpendicular_foot (P := P) (Q := Q) (R := R) hH4)
  -- 2. thm:pythagoras-at-foot, from H4, 1
  have s2 : dist P Q ^ 2 = dist P H ^ 2 + dist H Q ^ 2 := by exact (Parley.Proofs.Wiedijk.LawOfCosines.PythagorasAtFoot.pythagoras_at_foot (P := P) (Q := Q) (H := H) s1c hH4.1 s1d)
  -- 3. thm:distance-from-foot, from H4, 1
  have s3 : dist H R ^ 2 = dist H Q ^ 2 + dist Q R ^ 2 - 2 * (dist P Q * dist Q R * Real.cos (EuclideanGeometry.angle P Q R)) := by exact (Parley.Proofs.Wiedijk.LawOfCosines.DistanceFromFoot.distance_from_foot (P := P) (Q := Q) (R := R) (H := H) hH4 s1b s1c s1d s1e)
  -- 4. calculation
  calc dist R P ^ 2 = dist P H ^ 2 + dist H R ^ 2 := (by (have h := (Parley.Proofs.Wiedijk.LawOfCosines.PythagorasAtFoot.pythagoras_at_foot (P := P) (Q := R) (H := H) s1c hH4.2.2.1 s1e); rw [dist_comm P R] at h; exact h) : dist R P ^ 2 = dist P H ^ 2 + dist H R ^ 2)
    _ = dist P Q ^ 2 - dist H Q ^ 2 + dist H R ^ 2 := by linear_combination (-1) * s2
    _ = dist P Q ^ 2 + dist Q R ^ 2 - 2 * (dist P Q * dist Q R * Real.cos (EuclideanGeometry.angle P Q R)) := by linear_combination s3

end Parley.Proofs.Wiedijk.LawOfCosines.LawOfCosines

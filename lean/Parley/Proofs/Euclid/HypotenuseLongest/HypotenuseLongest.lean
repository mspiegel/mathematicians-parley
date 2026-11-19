module

public import Geometry
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
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
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.Pythagoras.Pythagoras

/-! Written from proofs/euclid/hypotenuse-longest.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.HypotenuseLongest.HypotenuseLongest

theorem hypotenuse_longest (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180) :
    dist A C < dist A B := by
  -- 1. axi:distance-positive P := B, Q := C, from H4
  have s1 : dist B C > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := B) (Q := C) hH4.2.1)
  -- 2. mun:square-positive x := |BC|
  have r23_1 : dist B C ≠ 0 := ne_of_gt (by linarith only [s1])
  have s2 : dist B C ^ 2 > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_positive (x := dist B C) r23_1)
  -- 3. inequalities
  have s3 : dist A C ^ 2 < dist A C ^ 2 + dist B C ^ 2 := by linarith only [s2]
  -- 4. calculation
  have s4 : dist A C ^ 2 < dist A B ^ 2 := by
    calc dist A C ^ 2 < dist A C ^ 2 + dist B C ^ 2 := s3
      _ = dist A B ^ 2 := by exact (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := A) (B := B) (C := C) hH4 hH5).symm
  -- 5. mun:square-less x := |AC|, y := |AB|, from 4
  have r38_1 : dist A C ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := A) (Q := C))
  have r38_2 : dist A B ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := A) (Q := B))
  exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := dist A C) (y := dist A B) r38_1 r38_2)).mpr s4

end Parley.Proofs.Euclid.HypotenuseLongest.HypotenuseLongest

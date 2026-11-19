module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry

/-! Written from proofs/euclid/distance-minus-four-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.DistanceMinusFourOne.DistanceMinusFourOne

theorem distance_minus_four_one :
    dist (Complex.mk (-4 : ℝ) (1 : ℝ)) (Complex.mk (3 : ℝ) (-4 : ℝ)) = Real.sqrt (74 : ℝ) := by
  -- 1. calculation
  calc dist (Complex.mk (-4 : ℝ) (1 : ℝ)) (Complex.mk (3 : ℝ) (-4 : ℝ)) = Real.sqrt ((-4 - 3) ^ 2 + (1 - -4) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_by_coordinates (a := (-4 : ℝ)) (b := (1 : ℝ)) (c := (3 : ℝ)) (d := (-4 : ℝ)))
    _ = Real.sqrt (74 : ℝ) := by norm_num

end Parley.Proofs.Euclid.DistanceMinusFourOne.DistanceMinusFourOne

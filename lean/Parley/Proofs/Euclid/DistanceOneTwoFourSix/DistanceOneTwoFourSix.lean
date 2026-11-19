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
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
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

/-! Written from proofs/euclid/distance-one-two-four-six.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.DistanceOneTwoFourSix.DistanceOneTwoFourSix

theorem distance_one_two_four_six :
    dist (Complex.mk (1 : ℝ) (2 : ℝ)) (Complex.mk (4 : ℝ) (6 : ℝ)) = 5 := by
  -- 1. calculation
  calc dist (Complex.mk (1 : ℝ) (2 : ℝ)) (Complex.mk (4 : ℝ) (6 : ℝ)) = Real.sqrt ((1 - 4) ^ 2 + (2 - 6) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_by_coordinates (a := (1 : ℝ)) (b := (2 : ℝ)) (c := (4 : ℝ)) (d := (6 : ℝ)))
    _ = Real.sqrt (25 : ℝ) := by norm_num
    _ = 5 := by
        have hv1 : Real.sqrt (25 : ℝ) = 5 := by rw [congrArg Real.sqrt (show (25 : ℝ) = 5 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 5 by norm_num)]
        linear_combination hv1

end Parley.Proofs.Euclid.DistanceOneTwoFourSix.DistanceOneTwoFourSix

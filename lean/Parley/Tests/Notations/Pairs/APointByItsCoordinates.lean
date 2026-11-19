module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Written from tests/notations/pairs.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Pairs.APointByItsCoordinates

theorem a_point_by_its_coordinates (A : ℂ) (hH1 : A ∈ (Set.univ : Set ℂ)) (B : ℂ) (hH2 : B ∈ (Set.univ : Set ℂ)) (hH3 : A = Complex.mk (1 : ℝ) (2 : ℝ)) (hH4 : dist A B = 3) :
    dist (Complex.mk (1 : ℝ) (2 : ℝ)) B = 3 := by
  -- 1. substitute A = (1, 2) (H3) into H4
  exact Eq.subst (motive := (fun t : ℂ => dist t B = 3)) hH3 hH4

end Parley.Tests.Notations.Pairs.APointByItsCoordinates

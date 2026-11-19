module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
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

/-! Written from tests/elaborator/a-point-said-back-over-the-plane.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APointSaidBackOverThePlane.APointSaidBackOverThePlane

theorem a_point_said_back_over_the_plane (P : ℂ) (Q : ℂ) (hH3 : dist P Q = 1) :
    (∃ H ∈ (Set.univ : Set ℂ), dist H Q = 1) := by
  -- 1. exhibit, from H3
  exact ⟨P, Set.mem_univ _, hH3⟩

end Parley.Tests.Elaborator.APointSaidBackOverThePlane.APointSaidBackOverThePlane

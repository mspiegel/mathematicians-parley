module

public import Geometry
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
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
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.Ruler

theorem ruler (A : ℂ) (B : ℂ) (hH3 : A ≠ B) :
    (∃ f : ℂ → ℝ, Set.MapsTo f (LeanBridges.Geometry.line A B) (Set.univ : Set ℝ) ∧ ((Set.MapsTo f (LeanBridges.Geometry.line A B) (Set.univ : Set ℝ) ∧ Set.InjOn f (LeanBridges.Geometry.line A B) ∧ Set.SurjOn f (LeanBridges.Geometry.line A B) (Set.univ : Set ℝ)) ∧ (∀ P ∈ LeanBridges.Geometry.line A B, ∀ Q ∈ LeanBridges.Geometry.line A B, dist P Q = abs (f P - f Q)))) := by
  -- 1. axi:geometry-ruler, from H3
  exact (Parley.Items.Stdlib.Geometry.axi_ruler (A := A) (B := B) hH3)

end Parley.Tests.Stdlib.Geometry.Ruler

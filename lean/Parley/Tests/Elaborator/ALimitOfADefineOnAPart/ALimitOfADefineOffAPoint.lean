module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/elaborator/a-limit-of-a-define-on-a-part.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ALimitOfADefineOnAPart.ALimitOfADefineOffAPoint

theorem a_limit_of_a_define_off_a_point (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (c : ℝ) (L : ℝ) (h : ℝ → ℝ) (hH4 : Set.MapsTo h (D \ ({c} : Set ℝ)) (Set.univ : Set ℝ)) (k : ℝ → ℝ) (hD1 : ∀ x : ℝ, x ∈ D \ ({c} : Set ℝ) → k x = h x + 1) (hH5 : D \ ({c} : Set ℝ) ⊆ (Set.univ : Set ℝ)) (hH6 : Set.MapsTo k (D \ ({c} : Set ℝ)) (Set.univ : Set ℝ)) (hH7 : Filter.Tendsto k (nhdsWithin c ((D \ ({c} : Set ℝ)) \ {c})) (nhds L)) :
    (∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D \ ({c} : Set ℝ), x ≠ c ∧ abs (x - c) < δ → abs (k x - L) < ε))) := by
  -- 1. def:limit-at D := D ∖ {c}, f := k, from H5, H6, H7
  exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := k) (D := D \ ({c} : Set ℝ)) hH5 (c := c) (L := L))).mp hH7

end Parley.Tests.Elaborator.ALimitOfADefineOnAPart.ALimitOfADefineOffAPoint

module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.DerivativeArctan

theorem derivative_arctan (E : Set ℝ) (hH1 : E ⊆ (Set.univ : Set ℝ)) (V : Set ℝ) (hH2 : V ⊆ E) (hH3 : IsOpen V) (h : ℝ → ℝ) (hH4 : Set.MapsTo h E (Set.univ : Set ℝ)) (hH5 : ∀ y ∈ E, h y = Real.arctan y) :
    (∀ x ∈ V, E ∈ nhds x ∧ DifferentiableAt ℝ h x) ∧ (∀ y ∈ V, (deriv h) y = 1 / (1 + y ^ 2)) := by
  -- 1. thm:trigonometry-derivative-arctan D := E, U := V, g := h, from H1, H2, H3, H5
  have s1a : ∀ x ∈ V, E ∈ nhds x ∧ DifferentiableAt ℝ h x := by exact (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side))
  have s1b : ∀ y ∈ V, (deriv h) y = 1 / (1 + y ^ 2) := by first | exact (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side)); parley_set_side)
  exact ⟨by parley_set_side, by parley_set_side⟩

end Parley.Tests.Stdlib.Trigonometry.DerivativeArctan

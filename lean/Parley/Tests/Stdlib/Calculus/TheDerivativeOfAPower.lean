module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
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
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.TheDerivativeOfAPower

theorem the_derivative_of_a_power (E : Set ℝ) (hH1 : E ⊆ (Set.univ : Set ℝ)) (V : Set ℝ) (hH2 : V ⊆ E) (hH3 : IsOpen V) (h : ℝ → ℝ) (hH4 : Set.MapsTo h E (Set.univ : Set ℝ)) (hH5 : ∀ y ∈ E, h y = y ^ (2 + 1)) :
    (∀ x ∈ V, E ∈ nhds x ∧ DifferentiableAt ℝ h x) ∧ (∀ y ∈ V, (deriv h) y = (2 + 1) * y ^ 2) := by
  -- 1. thm:derivative-power D := E, U := V, n := 2, g := h, from H1, H2, H3, H5
  have s1a : ∀ x ∈ V, E ∈ nhds x ∧ DifferentiableAt ℝ h x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_power_1 (g := h) (D := E) (U := V) hH1 hH2 hH3 (n := (2 : ℤ)) (by parley_set_side) (by simpa only [Int.reduceAdd, Int.reduceToNat, Nat.reduceAdd] using hH5))
  have s1b : ∀ y ∈ V, (deriv h) y = (2 + 1) * y ^ 2 := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_power_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (n := (2 : ℤ)) (by parley_set_side) (by simpa only [Int.reduceAdd, Int.reduceToNat, Nat.reduceAdd] using hH5)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_power_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (n := (2 : ℤ)) (by parley_set_side) (by simpa only [Int.reduceAdd, Int.reduceToNat, Nat.reduceAdd] using hH5))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_power_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (n := (2 : ℤ)) (by parley_set_side) (by simpa only [Int.reduceAdd, Int.reduceToNat, Nat.reduceAdd] using hH5)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_power_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (n := (2 : ℤ)) (by parley_set_side) (by simpa only [Int.reduceAdd, Int.reduceToNat, Nat.reduceAdd] using hH5)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_power_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (n := (2 : ℤ)) (by parley_set_side) (by simpa only [Int.reduceAdd, Int.reduceToNat, Nat.reduceAdd] using hH5)); parley_set_side)
  exact ⟨s1a, s1b⟩

end Parley.Tests.Stdlib.Calculus.TheDerivativeOfAPower

module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
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

/-! Written from proofs/setmm/identity-function-continuous.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.IdentityFunctionContinuous.IdentityFunctionContinuous

theorem identity_function_continuous (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (f : ℝ → ℝ) (hH2 : Set.MapsTo f D (Set.univ : Set ℝ)) (hH3 : ∀ x ∈ D, f x = x) :
    ContinuousOn f D := by
  -- 1. proof
  have s1 : ∀ a ∈ D, ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, abs (x - a) < δ → abs (f x - f a) < ε)) := by
    intro a hK1
    -- 1.1. proof
    intro ε
    intro hA1
    -- 1.1.1. proof
    have s1_1_1 : ∀ x ∈ D, abs (x - a) < ε → abs (f x - f a) < ε := by
      intro x hK3
      intro hA2
      -- 1.1.1.1. instantiate x := x in H3, from K3
      have s1_1_1_1 : f x = x := by exact (hH3 x (by parley_set_side))
      -- 1.1.1.2. instantiate x := a in H3, from K1
      have s1_1_1_2 : f a = a := by exact (hH3 a (by parley_set_side))
      -- 1.1.1.3. calculation
      have s1_1_1_3 : f x - f a = x - a := by
        calc f x - f a = x - f a := by parley_subst s1_1_1_1
          _ = x - a := by parley_subst s1_1_1_2
      -- 1.1.1.4. calculation
      calc abs (f x - f a) = abs (x - a) := by parley_subst s1_1_1_3
        _ < ε := by parley_set_side
    -- 1.1.2. exhibit, from A1, 1.1.1
    exact ⟨ε, ⟨hA1, s1_1_1⟩⟩
  -- 2. def:continuous-on, from H1, 1
  exact ((Parley.Items.Stdlib.Calculus.def_continuous_on (f := f) (D := D) hH1)).mpr s1

end Parley.Proofs.Setmm.IdentityFunctionContinuous.IdentityFunctionContinuous

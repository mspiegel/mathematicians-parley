module

public import ArithTactics
public import NormTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
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
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/constant-function-continuous.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ConstantFunctionContinuous.ConstantFunctionContinuous

theorem constant_function_continuous (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (k : ℝ) (f : ℝ → ℝ) (hH3 : Set.MapsTo f D (Set.univ : Set ℝ)) (hH4 : ∀ x ∈ D, f x = k) :
    ContinuousOn f D := by
  -- 1. proof
  have s1 : ∀ a ∈ D, ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, abs (x - a) < δ → abs (f x - f a) < ε)) := by
    intro a hK1
    -- 1.1. proof
    intro ε
    intro hA1
    -- 1.1.1. proof
    have s1_1_1 : ∀ x ∈ D, abs (x - a) < 1 → abs (f x - f a) < ε := by
      intro x hK3
      intro hA2
      -- 1.1.1.1. instantiate x := x in H4, from K3
      have s1_1_1_1 : f x = k := by exact (hH4 x (by parley_set_side))
      -- 1.1.1.2. instantiate x := a in H4, from K1
      have s1_1_1_2 : f a = k := by exact (hH4 a (by parley_set_side))
      -- 1.1.1.3. algebra, from 1.1.1.1, 1.1.1.2
      have s1_1_1_3 : f x - f a = 0 := by linear_combination (norm := parley_norm) s1_1_1_1 + (-1) * s1_1_1_2
      -- 1.1.1.4. calculation
      calc abs (f x - f a) = abs 0 := by (have h := congrArg (fun t : ℝ => abs t) s1_1_1_3; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 0 := by exact_mod_cast Parley.Items.Stdlib.Numbers.mun_abs_zero
        _ < ε := by parley_set_side
    -- 1.1.2. exhibit, from 1.1.1
    have r45_1 : (1 : ℤ) > 0 := by parley_arith
    exact ⟨(1 : ℝ), ⟨by parley_set_side, s1_1_1⟩⟩
  -- 2. def:continuous-on, from H1, 1
  exact ((Parley.Items.Stdlib.Calculus.def_continuous_on (f := f) (D := D) hH1)).mpr s1

end Parley.Proofs.Setmm.ConstantFunctionContinuous.ConstantFunctionContinuous

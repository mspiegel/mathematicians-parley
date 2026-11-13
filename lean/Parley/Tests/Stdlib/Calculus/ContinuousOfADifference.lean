module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ContinuousOfADifference

theorem continuous_of_a_difference (f : ℝ → ℝ) (hH2 : ContinuousOn f (Set.univ : Set ℝ)) (g : ℝ → ℝ) (hH4 : ContinuousOn g (Set.univ : Set ℝ)) (F : ℝ → ℝ) (hH6 : ∀ x : ℝ, F x = f x - g x) :
    ContinuousOn F (Set.univ : Set ℝ) := by
  -- 1. mun:subset-self X := ℝ
  have s1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  -- 2. thm:continuous-difference D := ℝ, from H2, H4, H6, 1
  exact (Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) s1 (by simpa only [Set.mem_univ, forall_const] using hH6) hH2 hH4)

end Parley.Tests.Stdlib.Calculus.ContinuousOfADifference

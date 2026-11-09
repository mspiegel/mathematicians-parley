module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from proofs/setmm/limit-add-constant.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitAddConstant.LimitAddConstant

theorem limit_add_constant (x : ℤ → ℝ) (L : ℝ) (C : ℝ) (hH4 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n : ℤ => (x n + C : ℝ)) Filter.atTop (nhds (L + C)) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n + C - (L + C)) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. def:tends-to, from H4
    have s1_1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < ε)) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp hH4
    -- 1.2. instantiate ε := ε in line 1.1, from A1
    have s1_2 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < ε) := by exact (s1_1 ε (by parley_side))
    -- 1.3. obtain N from line 1.2
    obtain ⟨N, s1_3a, s1_3b⟩ := s1_2
    -- 1.4. proof
    have s1_4 : ∀ n : ℤ, 0 < n → n ≥ N → abs (x n + C - (L + C)) < ε := by
      intro n hK2
      intro hA2
      -- 1.4.1. instantiate n := n in line 1.3, from A2
      have s1_4_1 : abs (x n - L) < ε := by exact (s1_3b n (by parley_side) (by parley_side))
      -- 1.4.2. substitute
      have c1 : x n - L = x n + C - (L + C) := by parley_ring
      have row1 : abs (x n + C - (L + C)) < ε := by parley_subst_at c1 s1_4_1
      exact row1
    -- 1.5. exhibit, from 1.4
    exact ⟨N, s1_3a, s1_4⟩
  -- 2. def:tends-to L := L + C, from 1
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => x n + C)) (L := L + C))).mpr s1

end Parley.Proofs.Setmm.LimitAddConstant.LimitAddConstant

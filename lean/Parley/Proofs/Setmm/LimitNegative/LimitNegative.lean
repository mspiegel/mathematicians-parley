module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/limit-negative.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitNegative.LimitNegative

theorem limit_negative (x : ℤ → ℝ) (L : ℝ) (hH3 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n : ℤ => (-x n : ℝ)) Filter.atTop (nhds (-L)) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (-x n - -L) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. def:tends-to, from H3
    have s1_1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < ε)) := by exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp hH3
    -- 1.2. instantiate ε := ε in line 1.1, from A1
    have s1_2 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < ε) := by exact (s1_1 ε hA1)
    -- 1.3. obtain N from line 1.2
    obtain ⟨N, s1_3a, s1_3b⟩ := s1_2
    -- 1.4. proof
    have s1_4 : ∀ n : ℤ, 0 < n → n ≥ N → abs (-x n - -L) < ε := by
      intro n hK2
      intro hA2
      -- 1.4.1. instantiate n := n in line 1.3, from A2
      have s1_4_1 : abs (x n - L) < ε := by exact (s1_3b n hK2 hA2)
      -- 1.4.2. membership, from H1
      -- 1.4.3. algebra
      have s1_4_3 : -x n - -L = -(x n - L) := by ring1
      -- 1.4.4. calculation
      have s1_4_4 : abs (-x n - -L) = abs (x n - L) := by
        calc abs (-x n - -L) = abs (-(x n - L)) := congrArg (fun t : ℝ => abs t) s1_4_3
          _ = abs (x n - L) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x n - L))
      -- 1.4.5. substitute |−x(n) − −L| = |x(n) − L| (line 1.4.4) into line 1.4.1
      exact Eq.subst (motive := (fun t : ℝ => t < ε)) s1_4_4.symm s1_4_1
    -- 1.5. exhibit, from 1.4
    exact ⟨N, s1_3a, s1_4⟩
  -- 2. def:tends-to L := −L, from 1
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => -x n)) (L := -L))).mpr s1

end Parley.Proofs.Setmm.LimitNegative.LimitNegative

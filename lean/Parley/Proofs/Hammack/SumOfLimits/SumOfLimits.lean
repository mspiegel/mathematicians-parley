module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/sum-of-limits.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfLimits.SumOfLimits

set_option maxHeartbeats 600000 in
theorem sum_of_limits (a : ℤ → ℝ) (b : ℤ → ℝ) (L : ℝ) (M : ℝ) (hH5 : Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds L)) (hH6 : Filter.Tendsto (fun n : ℤ => (b n : ℝ)) Filter.atTop (nhds M)) :
    Filter.Tendsto (fun n : ℤ => (a n + b n : ℝ)) Filter.atTop (nhds (L + M)) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n + b n - (L + M)) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. inequalities
    have s1_1 : ε / 2 > 0 := by parley_order
    -- 1.2. def:tends-to, from H5
    have s1_2 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - L) < ε)) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp hH5
    -- 1.3. def:tends-to x := b, L := M, from H6
    have s1_3 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (b n - M) < ε)) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := b) (L := M))).mp hH6
    -- 1.4. instantiate ε := ε/2 in line 1.2, from 1.1
    have s1_4 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - L) < ε / 2) := by exact (s1_2 (ε / 2) (by parley_side))
    -- 1.5. instantiate ε := ε/2 in line 1.3, from 1.1
    have s1_5 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (b n - M) < ε / 2) := by exact (s1_3 (ε / 2) (by parley_side))
    -- 1.6. obtain P from line 1.4
    obtain ⟨P, s1_6a, s1_6b⟩ := s1_4
    -- 1.7. obtain Q from line 1.5
    obtain ⟨Q, s1_7a, s1_7b⟩ := s1_5
    -- 1.8. inequalities, from 1.7
    have s1_8 : Q > 0 := by parley_order
    -- 1.9. inequalities
    have s1_9 : P + Q ≥ P := by parley_order
    -- 1.10. inequalities, from 1.6
    have s1_10 : P > 0 := by parley_order
    -- 1.11. inequalities
    have s1_11 : P + Q ≥ Q := by parley_order
    -- 1.12. proof
    have s1_12 : ∀ n : ℤ, 0 < n → n ≥ P + Q → abs (a n + b n - (L + M)) < ε := by
      intro n hK2
      intro hA2
      -- 1.12.1. transitivity, from A2, 1.9
      have s1_12_1 : n ≥ P := by parley_order
      -- 1.12.2. transitivity, from A2, 1.11
      have s1_12_2 : n ≥ Q := by parley_order
      -- 1.12.3. instantiate n := n in line 1.6, from 1.12.1
      have s1_12_3 : abs (a n - L) < ε / 2 := by exact (s1_6b n (by parley_side) (by parley_side))
      -- 1.12.4. instantiate n := n in line 1.7, from 1.12.2
      have s1_12_4 : abs (b n - M) < ε / 2 := by exact (s1_7b n (by parley_side) (by parley_side))
      -- 1.12.5. mun:abs-difference-lt x := a(n), c := L, δ := ε/2, from 1.12.3
      have s1_12_5 : L - ε / 2 < a n ∧ a n < L + ε / 2 := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a n) (c := L) (δ := ε / 2))).mp s1_12_3
      -- 1.12.6. mun:abs-difference-lt x := b(n), c := M, δ := ε/2, from 1.12.4
      have s1_12_6 : M - ε / 2 < b n ∧ b n < M + ε / 2 := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := b n) (c := M) (δ := ε / 2))).mp s1_12_4
      -- 1.12.7. inequalities, from 1.12.5, 1.12.6
      have s1_12_7 : L + M - ε < a n + b n := by parley_order
      -- 1.12.8. inequalities, from 1.12.5, 1.12.6
      have s1_12_8 : a n + b n < L + M + ε := by parley_order
      -- 1.12.9. join 1.12.7, 1.12.8
      have s1_12_9 : L + M - ε < a n + b n ∧ a n + b n < L + M + ε := by parley_side
      -- 1.12.10. mun:abs-difference-lt x := a(n) + b(n), c := L + M, δ := ε, from 1.12.9
      exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a n + b n) (c := L + M) (δ := ε))).mpr (by parley_side)
    -- 1.13. exhibit, from 1.12
    exact ⟨P + Q, by parley_side, s1_12⟩
  -- 2. def:tends-to L := L + M, from 1
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => a n + b n)) (L := L + M))).mpr s1

end Parley.Proofs.Hammack.SumOfLimits.SumOfLimits

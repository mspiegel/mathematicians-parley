module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/squeeze-for-sequences.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SqueezeForSequences.SqueezeForSequences

theorem squeeze_for_sequences (a : ℤ → ℝ) (b : ℤ → ℝ) (c : ℤ → ℝ) (L : ℝ) (hH5 : ∃ M : ℤ, ∀ n : ℤ, 0 < n → n > M → a n ≤ b n ∧ b n ≤ c n) (hH6 : Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds L)) (hH7 : Filter.Tendsto (fun n : ℤ => (c n : ℝ)) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n : ℤ => (b n : ℝ)) Filter.atTop (nhds L) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (b n - L) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. def:tends-to x := a, from H6
    have s1_1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - L) < ε)) := by exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp hH6
    -- 1.2. def:tends-to x := c, from H7
    have s1_2 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (c n - L) < ε)) := by exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := c) (L := L))).mp hH7
    -- 1.3. instantiate ε := ε in line 1.1, from A1
    have s1_3 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - L) < ε) := by exact (s1_1 ε hA1)
    -- 1.4. instantiate ε := ε in line 1.2, from A1
    have s1_4 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (c n - L) < ε) := by exact (s1_2 ε hA1)
    -- 1.5. obtain P from line 1.3
    obtain ⟨P, s1_5a, s1_5b⟩ := s1_3
    -- 1.6. obtain Q from line 1.4
    obtain ⟨Q, s1_6a, s1_6b⟩ := s1_4
    -- 1.7. obtain M from H5
    obtain ⟨M, s1_7⟩ := hH5
    -- 1.8. obtain R: thm:archimedean-natural x := M
    obtain ⟨R, s1_8a, s1_8b_obtained⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean_natural (x := (M : ℝ)))
    have s1_8b : R > M := by exact_mod_cast s1_8b_obtained
    -- 1.9. inequalities, from 1.6, 1.8
    have s1_9 : Q + R > 0 := by linarith only [s1_6a, s1_8a]
    -- 1.10. inequalities
    have s1_10 : P + Q + R ≥ P := by linarith only [s1_9]
    -- 1.11. inequalities, from 1.5, 1.8
    have s1_11 : P + R > 0 := by linarith only [s1_5a, s1_8a]
    -- 1.12. inequalities
    have s1_12 : P + Q + R ≥ Q := by linarith only [s1_11]
    -- 1.13. inequalities, from 1.5, 1.6
    have s1_13 : P + Q > 0 := by linarith only [s1_5a, s1_6a]
    -- 1.14. inequalities
    have s1_14 : P + Q + R > R := by linarith only [s1_13]
    -- 1.15. proof
    have s1_15 : ∀ n : ℤ, 0 < n → n ≥ P + Q + R → abs (b n - L) < ε := by
      intro n hK2
      intro hA2
      -- 1.15.1. transitivity, from A2, 1.10
      have s1_15_1 : n ≥ P := by exact le_trans s1_10 hA2
      -- 1.15.2. transitivity, from A2, 1.12
      have s1_15_2 : n ≥ Q := by exact le_trans s1_12 hA2
      -- 1.15.3. transitivity, from A2, 1.14, 1.8
      have s1_15_3 : n > M := by exact lt_of_lt_of_le (lt_trans s1_8b s1_14) hA2
      -- 1.15.4. instantiate n := n in line 1.5, from 1.15.1
      have s1_15_4 : abs (a n - L) < ε := by exact (s1_5b n hK2 s1_15_1)
      -- 1.15.5. instantiate n := n in line 1.6, from 1.15.2
      have s1_15_5 : abs (c n - L) < ε := by exact (s1_6b n hK2 s1_15_2)
      -- 1.15.6. instantiate n := n in line 1.7, from 1.15.3
      have s1_15_6 : a n ≤ b n ∧ b n ≤ c n := by exact (s1_7 n hK2 s1_15_3)
      -- 1.15.7. mun:abs-difference-lt x := a(n), c := L, δ := ε, from 1.15.4
      have s1_15_7 : L - ε < a n := by exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a n) (c := L) (δ := ε))).mp s1_15_4).1
      -- 1.15.8. mun:abs-difference-lt x := c(n), c := L, δ := ε, from 1.15.5
      have s1_15_8 : c n < L + ε := by exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := c n) (c := L) (δ := ε))).mp s1_15_5).2
      -- 1.15.9. transitivity, from 1.15.7, 1.15.6
      have s1_15_9 : L - ε < b n := by exact lt_of_lt_of_le s1_15_7 s1_15_6.1
      -- 1.15.10. transitivity, from 1.15.6, 1.15.8
      have s1_15_10 : b n < L + ε := by exact lt_of_le_of_lt s1_15_6.2 s1_15_8
      -- 1.15.11. join 1.15.9, 1.15.10
      have s1_15_11 : L - ε < b n ∧ b n < L + ε := ⟨s1_15_9, s1_15_10⟩
      -- 1.15.12. mun:abs-difference-lt x := b(n), c := L, δ := ε, from 1.15.11
      exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := b n) (c := L) (δ := ε))).mpr ⟨s1_15_11.1, s1_15_11.2⟩
    -- 1.16. exhibit, from 1.15
    exact ⟨P + Q + R, add_pos (add_pos (s1_5a) (s1_6a)) (s1_8a), s1_15⟩
  -- 2. def:tends-to x := b, from 1
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := b) (L := L))).mpr s1

end Parley.Proofs.Hammack.SqueezeForSequences.SqueezeForSequences

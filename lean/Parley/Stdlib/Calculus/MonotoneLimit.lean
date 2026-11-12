module

public import InstanceTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Batteries.Tactic.Init
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
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
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Stdlib.Calculus.IncreasingTerms

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.MonotoneLimit

theorem monotone_limit (x : ℤ → ℝ) (hH2 : ∀ n : ℤ, 0 < n → x n ≤ x (n + 1)) (B : ℝ) (hH4 : ∀ n : ℤ, 0 < n → x n ≤ B) :
    (∃ L : ℝ, Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) := by
  -- 1. mun:subset-self
  have s1 : {n : ℤ | 0 < n} ⊆ {n : ℤ | 0 < n} := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := {n : ℤ | 0 < n}))
  -- 2. mun:image-within, from H1
  have s2 : x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_image_within (X := (Set.univ : Set ℤ)) (W := (Set.univ : Set ℝ)) (Y := {n : ℤ | 0 < n}) (f := x) (by parley_whole_side))
  -- 3. mun:value-in-image s := 1, from H1, 1
  have s3 : x 1 ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}) := by
    have hI : x 1 ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}) := by parley_instance_cast ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := (1 : ℤ)) (W := Set.univ) s1 (by parley_whole_side) (by parley_whole_side)))
    exact hI
  -- 4. proof
  have s4 : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ B := by
    intro s hK1
    -- 4.1. obtain k: def:image u := s, from H1, K1, 1
    obtain ⟨k, s4_1a, s4_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (u := s) (W := Set.univ) s1 (by parley_whole_side))).mp (by parley_set_side)
    -- 4.2. instantiate n := k in H4
    have s4_2 : x k ≤ B := by exact (hH4 k s4_1a)
    -- 4.3. transitivity, from 4.1, 4.2
    exact Eq.trans_le s4_1b s4_2
  -- 5. def:upper-bound, from 4
  have s5 : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ B := by parley_set_side
  -- 6. obtain c: axi:completeness, from 2, 3, 5
  obtain ⟨c, s6⟩ := (Parley.Items.Stdlib.Calculus.axi_completeness (S := x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n})) s2 (by parley_set_side) (by parley_set_side))
  -- 7. def:least-upper-bound, from 6
  have s7a : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ c := by parley_set_side
  have s7b : ∀ u : ℝ, (∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ u) → c ≤ u := by parley_set_side
  -- 8. def:upper-bound, from 7
  have s8 : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ c := by parley_set_side
  -- 9. mun:increasing-terms, from H2
  have s9 : ∀ n : ℤ, 0 < n → (∀ m : ℤ, 0 < m → m ≤ n → x m ≤ x n) := by exact (Parley.Stdlib.Calculus.IncreasingTerms.increasing_terms (x := x) hH2)
  -- 10. proof
  have s10 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - c) < ε)) := by
    intro ε
    intro hA1
    -- 10.1. inequalities
    have s10_1 : c - ε < c := by linarith only [hA1]
    -- 10.2. contradiction
    have s10_2 : ∃ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), c - ε < s := by
      by_contra hS
      -- 10.2.1. proof
      have s10_2_1 : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ c - ε := by
        intro s hK2
        by_contra hS2
        -- 10.2.1.1. mun:in-subset, from K2, 2
        -- 10.2.1.2. inequalities, from S2, 10.2.1.1
        have s10_2_1_2 : c - ε < s := by linarith only [hS2]
        -- 10.2.1.3. exhibit, from K2, 10.2.1.2
        have s10_2_1_3 : ∃ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), c - ε < s := ⟨s, hK2, s10_2_1_2⟩
        exact hS s10_2_1_3
      -- 10.2.2. def:upper-bound, from 10.2.1
      have s10_2_2 : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ c - ε := by parley_set_side
      -- 10.2.3. instantiate u := c − ε in line 7, from 10.2.2
      have s10_2_3 : c ≤ c - ε := by exact (s7b (c - ε) s10_2_2)
      -- 10.2.4. inequalities, from 10.1
      have s10_2_4 : ¬ c ≤ c - ε := by linarith only [s10_1]
      exact s10_2_4 s10_2_3
    -- 10.3. obtain s from line 10.2
    obtain ⟨s, s10_3a, s10_3b⟩ := s10_2
    -- 10.4. obtain N: def:image u := s, from H1, 1, 10.3
    obtain ⟨N, s10_4a, s10_4b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (u := s) (W := Set.univ) s1 (by parley_whole_side))).mp (by parley_set_side)
    -- 10.5. transitivity, from 10.3, 10.4
    have s10_5 : c - ε < x N := by exact LT.lt.trans_eq s10_3b s10_4b
    -- 10.6. inequalities
    have s10_6 : c < c + ε := by linarith only [hA1]
    -- 10.7. proof
    have s10_7 : ∀ n : ℤ, 0 < n → n ≥ N → abs (x n - c) < ε := by
      intro n hK2
      intro hA2
      -- 10.7.1. inequalities
      have s10_7_1 : N ≤ n := by linarith only [hA2]
      -- 10.7.2. instantiate m := N in line 9, from 10.7.1
      have s10_7_2 : x N ≤ x n := by exact ((s9 n hK2) N s10_4a s10_7_1)
      -- 10.7.3. mun:value-in-image s := n, from H1, 1
      have s10_7_3 : x n ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}) := by
        have hI : x n ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}) := by parley_instance_cast ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := n) (W := Set.univ) s1 (by parley_whole_side) (by parley_whole_side)))
        exact hI
      -- 10.7.4. instantiate s := x(n) in line 8, from 10.7.3
      have s10_7_4 : x n ≤ c := by exact (s8 (x n) s10_7_3)
      -- 10.7.5. transitivity, from 10.5, 10.7.2
      have s10_7_5 : c - ε < x n := by exact lt_of_lt_of_le s10_5 s10_7_2
      -- 10.7.6. transitivity, from 10.7.4, 10.6
      have s10_7_6 : x n < c + ε := by exact lt_of_le_of_lt s10_7_4 s10_6
      -- 10.7.7. join 10.7.5, 10.7.6
      have s10_7_7 : c - ε < x n ∧ x n < c + ε := ⟨s10_7_5, s10_7_6⟩
      -- 10.7.8. mun:abs-difference-lt x := x(n), δ := ε, from 10.7.7
      exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x n) (c := c) (δ := ε))).mpr ⟨s10_7_7.1, s10_7_7.2⟩
    -- 10.8. exhibit, from 10.7
    exact ⟨N, s10_4a, s10_7⟩
  -- 11. def:tends-to L := c, from 10
  have s11 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds c) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := c))).mpr s10
  -- 12. exhibit, from 11
  exact ⟨c, s11⟩

end Parley.Stdlib.Calculus.MonotoneLimit

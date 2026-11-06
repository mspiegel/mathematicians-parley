module

public import ArithTactics
public import OrderTactics
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
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Stdlib.Calculus.IncreasingTerms

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.MonotoneLimit

set_option maxHeartbeats 800000 in
theorem monotone_limit (x : ℤ → ℝ) (hH2 : ∀ n : ℤ, 0 < n → x n ≤ x (n + 1)) (B : ℝ) (hH4 : ∀ n : ℤ, 0 < n → x n ≤ B) :
    (∃ L : ℝ, Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) := by
  -- 1. mun:subset-self
  have s1 : {n : ℤ | 0 < n} ⊆ {n : ℤ | 0 < n} := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := {n : ℤ | 0 < n})) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := {n : ℤ | 0 < n}))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := {n : ℤ | 0 < n})) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := {n : ℤ | 0 < n})) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := {n : ℤ | 0 < n})); parley_set_side)
  -- 2. mun:image-within, from H1
  have s2 : x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_image_within (X := (Set.univ : Set ℤ)) (W := (Set.univ : Set ℝ)) (Y := {n : ℤ | 0 < n}) (f := x) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_image_within (X := (Set.univ : Set ℤ)) (W := (Set.univ : Set ℝ)) (Y := {n : ℤ | 0 < n}) (f := x) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_image_within (X := (Set.univ : Set ℤ)) (W := (Set.univ : Set ℝ)) (Y := {n : ℤ | 0 < n}) (f := x) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_image_within (X := (Set.univ : Set ℤ)) (W := (Set.univ : Set ℝ)) (Y := {n : ℤ | 0 < n}) (f := x) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_image_within (X := (Set.univ : Set ℤ)) (W := (Set.univ : Set ℝ)) (Y := {n : ℤ | 0 < n}) (f := x) (by parley_whole_side)); parley_set_side)
  -- 3. mun:value-in-image s := 1, from H1, 1
  have s3 : x 1 ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := (1 : ℤ)) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := (1 : ℤ)) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := (1 : ℤ)) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := (1 : ℤ)) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := (1 : ℤ)) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  -- 4. proof
  have s4 : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ B := by
    intro s hK1
    -- 4.1. obtain k: def:image u := s, from H1, K1, 1
    obtain ⟨k, s4_1a, s4_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (u := s) (W := Set.univ) (by parley_whole_side) (by parley_whole_side))).mp (by parley_set_side)
    -- 4.2. instantiate n := k in H4
    have s4_2 : x k ≤ B := by first | linarith [(hH4 k (by parley_set_side))] | (have h := (hH4 k (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (hH4 k (by parley_set_side)) | (have h := (hH4 k (by parley_set_side)); parley_set_side)
    -- 4.3. transitivity, from 4.1, 4.2
    have s4_3 : s ≤ B := by parley_order
    all_goals exact s4_3
  -- 5. def:upper-bound, from 4
  have s5 : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ B := by parley_set_side
  -- 6. obtain c: axi:completeness, from 2, 3, 5
  obtain ⟨c, ⟨s6, _⟩⟩ := (Parley.Items.Stdlib.Calculus.axi_completeness (S := x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n})) s2 (by parley_set_side) (by parley_set_side))
  -- 7. def:least-upper-bound, from 6
  have s7a : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ c := by parley_set_side
  have s7b : ∀ u : ℝ, (∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ u) → c ≤ u := by parley_set_side
  -- 8. def:upper-bound, from 7
  have s8 : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ c := by parley_set_side
  -- 9. mun:increasing-terms, from H2
  have s9 : ∀ n : ℤ, 0 < n → (∀ m : ℤ, 0 < m → m ≤ n → x m ≤ x n) := by first | exact (Parley.Stdlib.Calculus.IncreasingTerms.increasing_terms (x := x) hH2) | exact ((Parley.Stdlib.Calculus.IncreasingTerms.increasing_terms (x := x) hH2)).symm | simpa using (Parley.Stdlib.Calculus.IncreasingTerms.increasing_terms (x := x) hH2) | exact_mod_cast (Parley.Stdlib.Calculus.IncreasingTerms.increasing_terms (x := x) hH2) | (have h := (Parley.Stdlib.Calculus.IncreasingTerms.increasing_terms (x := x) hH2); parley_set_side)
  -- 10. proof
  have s10 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - c) < ε)) := by
    intro ε
    intro hA1
    -- 10.1. inequalities
    have s10_1 : c - ε < c := by parley_order
    -- 10.2. contradiction
    have s10_2 : ∃ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), c - ε < s := by
      by_contra hc_hS
      have hS : ¬ (∃ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), c - ε < s) := by parley_suppose hc_hS
      -- 10.2.1. proof
      have s10_2_1 : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ c - ε := by
        intro s hK2
        by_contra hc_hS2
        have hS2 : ¬ s ≤ c - ε := by parley_suppose hc_hS2
        -- 10.2.1.1. mun:in-subset, from K2, 2
        -- 10.2.1.2. inequalities, from S2, 10.2.1.1
        have s10_2_1_2 : c - ε < s := by parley_order
        -- 10.2.1.3. exhibit, from K2, 10.2.1.2
        have s10_2_1_3 : ∃ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), c - ε < s := ⟨s, by parley_set_side, by parley_set_side⟩
        all_goals parley_set_side
      -- 10.2.2. def:upper-bound, from 10.2.1
      have s10_2_2 : ∀ s ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}), s ≤ c - ε := by parley_set_side
      -- 10.2.3. instantiate u := c − ε in line 7, from 10.2.2
      have s10_2_3 : c ≤ c - ε := by first | linarith [(s7b (c - ε) (by parley_set_side))] | (have h := (s7b (c - ε) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s7b (c - ε) (by parley_set_side)) | (have h := (s7b (c - ε) (by parley_set_side)); parley_set_side)
      -- 10.2.4. inequalities, from 10.1
      have s10_2_4 : ¬ c ≤ c - ε := by parley_set_side
      all_goals parley_set_side
    -- 10.3. obtain s from line 10.2
    obtain ⟨s, s10_3a, s10_3b⟩ := s10_2
    -- 10.4. obtain N: def:image u := s, from H1, 1, 10.3
    obtain ⟨N, s10_4a, s10_4b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (u := s) (W := Set.univ) (by parley_whole_side) (by parley_whole_side))).mp (by parley_set_side)
    -- 10.5. transitivity, from 10.3, 10.4
    have s10_5 : c - ε < x N := by parley_order
    -- 10.6. inequalities
    have s10_6 : c < c + ε := by parley_order
    -- 10.7. proof
    have s10_7 : ∀ n : ℤ, 0 < n → n ≥ N → abs (x n - c) < ε := by
      intro n hK2
      intro hA2
      -- 10.7.1. inequalities
      have s10_7_1 : N ≤ n := by parley_order
      -- 10.7.2. instantiate m := N in line 9, from 10.7.1
      have s10_7_2 : x N ≤ x n := by first | linarith [(s9 n (by parley_set_side) N (by parley_set_side) (by parley_set_side))] | (have h := (s9 n (by parley_set_side) N (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s9 n (by parley_set_side) N (by parley_set_side) (by parley_set_side)) | (have h := (s9 n (by parley_set_side) N (by parley_set_side) (by parley_set_side)); parley_set_side)
      -- 10.7.3. mun:value-in-image s := n, from H1, 1
      have s10_7_3 : x n ∈ x '' ((Set.univ : Set ℤ) ∩ {n : ℤ | 0 < n}) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := n) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := n) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := n) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := n) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := {n : ℤ | 0 < n}) (Y := {n : ℤ | 0 < n}) (f := x) (s := n) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
      -- 10.7.4. instantiate s := x(n) in line 8, from 10.7.3
      have s10_7_4 : x n ≤ c := by first | linarith [(s8 (x n) (by parley_set_side))] | (have h := (s8 (x n) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s8 (x n) (by parley_set_side)) | (have h := (s8 (x n) (by parley_set_side)); parley_set_side)
      -- 10.7.5. transitivity, from 10.5, 10.7.2
      have s10_7_5 : c - ε < x n := by parley_order
      -- 10.7.6. transitivity, from 10.7.4, 10.6
      have s10_7_6 : x n < c + ε := by parley_order
      -- 10.7.7. join 10.7.5, 10.7.6
      have s10_7_7 : c - ε < x n ∧ x n < c + ε := by parley_set_side
      -- 10.7.8. mun:abs-difference-lt x := x(n), δ := ε, from 10.7.7
      have s10_7_8 : abs (x n - c) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x n) (c := c) (δ := ε))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x n) (c := c) (δ := ε))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    -- 10.8. exhibit, from 10.7
    have s10_8 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - c) < ε) := ⟨N, by parley_set_side, by parley_set_side⟩
    all_goals parley_set_side
  -- 11. def:tends-to L := c, from 10
  have s11 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds c) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := c))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := c))).mpr (by parley_set_side); parley_set_side)
  -- 12. exhibit, from 11
  have s12 : ∃ L : ℝ, Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L) := ⟨c, by parley_set_side⟩
  all_goals exact s12

end Parley.Stdlib.Calculus.MonotoneLimit

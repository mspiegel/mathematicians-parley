module

public import Batteries.Tactic.Init
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Parley.Items.Proofs.Wiedijk.ErdosSzekeres
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.ErdosSzekeres.LongestRuns

/-! Written from proofs/wiedijk/erdos-szekeres.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.ErdosSzekeres.ErdosSzekeres

theorem erdos_szekeres (r : ℤ) (hH1 : 0 < r) (s : ℤ) (hH2 : 0 < s) (N : ℤ) (hH3 : 0 < N) (a : ℤ → ℝ) (hH4 : Set.MapsTo a (Set.Icc (1 : ℤ) N : Set ℤ) (Set.univ : Set ℝ) ∧ Set.InjOn a (Set.Icc (1 : ℤ) N : Set ℤ)) (hH5 : (r - 1) * (s - 1) < N) :
    (∃ S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ), r ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i < a j) ∨ s ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i > a j)) := by
  -- 1. contradiction
  by_contra hS1
  -- 1.1. contradiction
  have s1_1 : ¬ (∃ S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ), r ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i < a j)) := by
    intro (hS2 : ∃ S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ), r ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i < a j))
    -- 1.1.1. obtain T from S2
    obtain ⟨T, _, ⟨s1_1_1a, s1_1_1b⟩⟩ := hS2
    -- 1.1.2. mun:or-left, from 1.1.1
    have s1_1_2 : r ≤ (T.ncard : ℤ) ∧ (∀ i ∈ T, ∀ j ∈ T, i < j → a i < a j) ∨ s ≤ (T.ncard : ℤ) ∧ (∀ i ∈ T, ∀ j ∈ T, i < j → a i > a j) := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := r ≤ (T.ncard : ℤ) ∧ (∀ i ∈ T, ∀ j ∈ T, i < j → a i < a j)) (Q := s ≤ (T.ncard : ℤ) ∧ (∀ i ∈ T, ∀ j ∈ T, i < j → a i > a j)) s1_1_1b)
    -- 1.1.3. exhibit, from 1.1.1, 1.1.2
    have s1_1_3 : ∃ S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ), r ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i < a j) ∨ s ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i > a j) := ⟨T, s1_1_1a, s1_1_2⟩
    exact hS1 s1_1_3
  set b : ℤ → ℝ := fun i : ℤ => -a i with hD3
  -- 1.2. membership, from D3
  -- 1.3. mun:function-into, from 1.2
  -- 1.4. contradiction
  have s1_4 : ¬ (∃ S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ), s ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → b i < b j)) := by
    intro (hS3 : ∃ S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ), s ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → b i < b j))
    -- 1.4.1. obtain T from S3
    obtain ⟨T, _, ⟨s1_4_1a, s1_4_1b⟩⟩ := hS3
    -- 1.4.2. D1, from 1.4.1
    have s1_4_2 : s ≤ (T.ncard : ℤ) ∧ (∀ i ∈ T, ∀ j ∈ T, i < j → b i < b j) := s1_4_1b
    -- 1.4.3. proof
    have s1_4_3 : ∀ i ∈ T, ∀ j ∈ T, i < j → a i > a j := by
      intro i hK1
      intro j hK2
      intro hK3
      -- 1.4.3.1. mun:in-subset, from K1, 1.4.1
      have s1_4_3_1 : i ∈ Finset.Icc (1 : ℤ) N := by
        have hI : i ∈ Finset.Icc (1 : ℤ) N := by (have h := ((Parley.Items.Stdlib.Sets.mun_in_subset (X := T) (Y := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := i) s1_4_1a hK1)); simp only [Finset.mem_Icc]; exact h)
        exact hI
      -- 1.4.3.2. mun:in-subset, from K2, 1.4.1
      have s1_4_3_2 : j ∈ Finset.Icc (1 : ℤ) N := by
        have hI : j ∈ Finset.Icc (1 : ℤ) N := by (have h := ((Parley.Items.Stdlib.Sets.mun_in_subset (X := T) (Y := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := j) s1_4_1a hK2)); simp only [Finset.mem_Icc]; exact h)
        exact hI
      -- 1.4.3.3. D3, from 1.4.3.1
      have s1_4_3_3 : b i = -a i := by simp (disch := omega) only [hD3]
      -- 1.4.3.4. D3, from 1.4.3.2
      have s1_4_3_4 : b j = -a j := by simp (disch := omega) only [hD3]
      -- 1.4.3.5. calculation
      have s1_4_3_5 : -a i < -a j := by
        calc -a i = b i := s1_4_3_3.symm
          _ < b j := by exact (s1_4_2.2 i hK1 j hK2 hK3)
          _ = -a j := s1_4_3_4
      -- 1.4.3.6. inequalities
      linarith only [s1_4_3_5]
    -- 1.4.4. D2, from 1.4.2, 1.4.3
    have s1_4_4 : s ≤ (T.ncard : ℤ) ∧ (∀ i ∈ T, ∀ j ∈ T, i < j → a i > a j) := ⟨s1_4_2.1, s1_4_3⟩
    -- 1.4.5. mun:or-right, from 1.4.4
    have s1_4_5 : r ≤ (T.ncard : ℤ) ∧ (∀ i ∈ T, ∀ j ∈ T, i < j → a i < a j) ∨ s ≤ (T.ncard : ℤ) ∧ (∀ i ∈ T, ∀ j ∈ T, i < j → a i > a j) := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := r ≤ (T.ncard : ℤ) ∧ (∀ i ∈ T, ∀ j ∈ T, i < j → a i < a j)) (Q := s ≤ (T.ncard : ℤ) ∧ (∀ i ∈ T, ∀ j ∈ T, i < j → a i > a j)) s1_4_4)
    -- 1.4.6. exhibit, from 1.4.1, 1.4.5
    have s1_4_6 : ∃ S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ), r ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i < a j) ∨ s ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i > a j) := ⟨T, s1_4_1a, s1_4_5⟩
    exact hS1 s1_4_6
  -- 1.5. obtain L: thm:longest-runs c := a, from 1.1
  obtain ⟨L, s1_5a, s1_5b⟩ := (Parley.Proofs.Wiedijk.ErdosSzekeres.LongestRuns.longest_runs (N := N) hH3 (r := r) hH1 (c := a) s1_1)
  -- 1.6. obtain M: thm:longest-runs c := b, r := s, from 1.3, 1.4
  obtain ⟨M, s1_6a, s1_6b⟩ := (Parley.Proofs.Wiedijk.ErdosSzekeres.LongestRuns.longest_runs (N := N) hH3 (r := s) hH2 (c := b) s1_4)
  set f : ℤ → ℤ × ℤ := fun i : ℤ => (L i, M i) with hD4
  -- 1.7. proof
  have s1_7 : ∀ i : ℤ, i ∈ Finset.Icc 1 N → f i ∈ (Set.Icc (1 : ℤ) (r - 1) : Set ℤ) ×ˢ (Set.Icc (1 : ℤ) (s - 1) : Set ℤ) := by
    intro i hK4
    have hK4_bounds := Finset.mem_Icc.mp hK4
    -- 1.7.1. mun:function-value f := L, from K4
    have s1_7_1 : L i ∈ Finset.Icc (1 : ℤ) (r - 1) := by
      have hI : L i ∈ Finset.Icc (1 : ℤ) (r - 1) := by (have h := ((Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) N : Set ℤ)) (E := (Set.Icc (1 : ℤ) (r - 1) : Set ℤ)) (f := L) (x := i) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hK4) s1_5a)); simp only [Finset.mem_Icc]; exact h)
      exact hI
    -- 1.7.2. mun:function-value f := M, from K4
    have s1_7_2 : M i ∈ Finset.Icc (1 : ℤ) (s - 1) := by
      have hI : M i ∈ Finset.Icc (1 : ℤ) (s - 1) := by (have h := ((Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) N : Set ℤ)) (E := (Set.Icc (1 : ℤ) (s - 1) : Set ℤ)) (f := M) (x := i) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hK4) s1_6a)); simp only [Finset.mem_Icc]; exact h)
      exact hI
    -- 1.7.3. mun:pair-in-product, from 1.7.1, 1.7.2
    have s1_7_3 : (L i, M i) ∈ (Set.Icc (1 : ℤ) (r - 1) : Set ℤ) ×ˢ (Set.Icc (1 : ℤ) (s - 1) : Set ℤ) := ((Parley.Items.Stdlib.Sets.mun_pair_in_product (X := (Set.Icc (1 : ℤ) (r - 1) : Set ℤ)) (Y := (Set.Icc (1 : ℤ) (s - 1) : Set ℤ)) (a := L i) (b := M i))).mpr ⟨by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_7_1, by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_7_2⟩
    -- 1.7.4. D4, from K4
    have s1_7_4 : f i = (L i, M i) := by simp (disch := omega) only [hD4]
    -- 1.7.5. substitute f(i) = (L(i), M(i)) (line 1.7.4) into line 1.7.3
    exact Eq.subst (motive := (fun t : ℤ × ℤ => t ∈ (Set.Icc (1 : ℤ) (r - 1) : Set ℤ) ×ˢ (Set.Icc (1 : ℤ) (s - 1) : Set ℤ))) s1_7_4.symm s1_7_3
  -- 1.8. mun:function-into, from 1.7
  have s1_8 : Set.MapsTo f (Set.Icc (1 : ℤ) N : Set ℤ) ((Set.Icc (1 : ℤ) (r - 1) : Set ℤ) ×ˢ (Set.Icc (1 : ℤ) (s - 1) : Set ℤ)) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (Y := (Set.Icc (1 : ℤ) (r - 1) : Set ℤ) ×ˢ (Set.Icc (1 : ℤ) (s - 1) : Set ℤ)) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_7))
  -- 1.9. def:one-to-one, from H4
  have s1_9 : ∀ x : ℤ, x ∈ Finset.Icc 1 N → (∀ y : ℤ, y ∈ Finset.Icc 1 N → a x = a y → x = y) := by
    have hI : ∀ s : ℤ, s ∈ Finset.Icc 1 N → (∀ t : ℤ, t ∈ Finset.Icc 1 N → a s = a t → s = t) := by (have h := ((((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (Y := (Set.univ : Set ℝ)) (f := a) (Set.mapsTo_univ _ _))).mp hH4).2); simp only [Finset.mem_Icc]; exact_mod_cast h)
    exact hI
  -- 1.10. proof
  have s1_10 : ∀ i : ℤ, i ∈ Finset.Icc 1 N → (∀ j : ℤ, j ∈ Finset.Icc 1 N → i < j → ¬ f i = f j) := by
    intro i hK5
    have hK5_bounds := Finset.mem_Icc.mp hK5
    intro j hK6
    have hK6_bounds := Finset.mem_Icc.mp hK6
    intro hK7
    -- 1.10.1. inequalities
    have s1_10_1 : i ≠ j := ne_of_lt (by linarith only [hK7])
    -- 1.10.2. contradiction
    have s1_10_2 : a i ≠ a j := by
      intro hS4
      -- 1.10.2.1. instantiate x := i, y := j in line 1.9, from K5, K6, S4
      have s1_10_2_1 : i = j := by exact (s1_9 i hK5 j hK6 hS4)
      exact s1_10_1 s1_10_2_1
    -- 1.10.3. mun:unequal-cases x := a(i), y := a(j), from 1.10.2
    have s1_10_3 : a i < a j ∨ a j < a i := by exact ((Parley.Items.Stdlib.Numbers.mun_unequal_cases (x := a i) (y := a j))).mp s1_10_2
    -- 1.10.4. cases, from 1.10.3
    rcases s1_10_3 with hC1 | hC2
    · skip
      -- 1.10.4.1. instantiate i := i, j := j in line 1.5, from C1, K5, K6, K7
      have s1_10_4_1 : L i < L j := by exact (s1_5b i hK5 j hK6 ⟨hK7, hC1⟩)
      -- 1.10.4.2. inequalities
      have s1_10_4_2 : L i ≠ L j := ne_of_lt (by linarith only [s1_10_4_1])
      -- 1.10.4.3. contradiction
      intro hS5
      -- 1.10.4.3.1. mun:pair-parts-equal, from D4, K5, K6, S5
      have s1_10_4_3_1 : L i = L j ∧ M i = M j := by
        have hI : L i = L j ∧ M i = M j := by exact_mod_cast (((Parley.Items.Stdlib.Sets.mun_pair_parts_equal (a := (L i : ℂ)) (b := (M i : ℂ)) (c := (L j : ℂ)) (d := (M j : ℂ)))).mp (by (have h := hS5; simp only [hD4, Prod.mk.injEq] at h ⊢; exact_mod_cast h)))
        exact hI
      -- 1.10.4.3.2. restate 1.10.4.3.1
      have s1_10_4_3_2 : L i = L j := by exact s1_10_4_3_1.1
      exact s1_10_4_2 s1_10_4_3_2
    · skip
      -- 1.10.4.4. D3, from K5
      have s1_10_4_4 : b i = -a i := by simp (disch := omega) only [hD3]
      -- 1.10.4.5. D3, from K6
      have s1_10_4_5 : b j = -a j := by simp (disch := omega) only [hD3]
      -- 1.10.4.6. inequalities
      have s1_10_4_6 : -a i < -a j := by linarith only [hC2]
      -- 1.10.4.7. calculation
      have s1_10_4_7 : b i < b j := by
        calc b i = -a i := s1_10_4_4
          _ < -a j := s1_10_4_6
          _ = b j := s1_10_4_5.symm
      -- 1.10.4.8. instantiate i := i, j := j in line 1.6, from K5, K6, K7, 1.10.4.7
      have s1_10_4_8 : M i < M j := by exact (s1_6b i hK5 j hK6 ⟨hK7, s1_10_4_7⟩)
      -- 1.10.4.9. inequalities
      have s1_10_4_9 : M i ≠ M j := ne_of_lt (by linarith only [s1_10_4_8])
      -- 1.10.4.10. contradiction
      intro hS6
      -- 1.10.4.10.1. mun:pair-parts-equal, from D4, K5, K6, S6
      have s1_10_4_10_1 : L i = L j ∧ M i = M j := by
        have hI : L i = L j ∧ M i = M j := by exact_mod_cast (((Parley.Items.Stdlib.Sets.mun_pair_parts_equal (a := (L i : ℂ)) (b := (M i : ℂ)) (c := (L j : ℂ)) (d := (M j : ℂ)))).mp (by (have h := hS6; simp only [hD4, Prod.mk.injEq] at h ⊢; exact_mod_cast h)))
        exact hI
      -- 1.10.4.10.2. restate 1.10.4.10.1
      have s1_10_4_10_2 : M i = M j := by exact s1_10_4_10_1.2
      exact s1_10_4_9 s1_10_4_10_2
  -- 1.11. proof
  have s1_11 : ∀ i : ℤ, i ∈ Finset.Icc 1 N → (∀ j : ℤ, j ∈ Finset.Icc 1 N → f i = f j → i = j) := by
    intro i hK8
    have hK8_bounds := Finset.mem_Icc.mp hK8
    intro j hK9
    have hK9_bounds := Finset.mem_Icc.mp hK9
    intro hK10
    -- 1.11.1. axi:excluded-middle P := i = j
    have s1_11_1 : i = j ∨ i ≠ j := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = j))
    -- 1.11.2. cases, from 1.11.1
    rcases s1_11_1 with hC3 | hC4
    · skip
      exact hC3
    · skip
      -- 1.11.2.1. mun:unequal-cases x := i, y := j, from C4
      have s1_11_2_1 : i < j ∨ j < i := by exact ((Parley.Items.Stdlib.Numbers.mun_unequal_cases (x := i) (y := j))).mp hC4
      -- 1.11.2.2. cases, from 1.11.2.1
      rcases s1_11_2_1 with hC5 | hC6
      · skip
        -- 1.11.2.2.1. instantiate i := i, j := j in line 1.10, from C5, K8, K9
        have s1_11_2_2_1 : ¬ f i = f j := by exact (s1_10 i hK8 j hK9 hC5)
        exact absurd hK10 s1_11_2_2_1
      · skip
        -- 1.11.2.2.2. instantiate i := j, j := i in line 1.10, from C6, K8, K9
        have s1_11_2_2_2 : ¬ f j = f i := by exact (s1_10 j hK9 i hK8 hC6)
        exact absurd hK10.symm s1_11_2_2_2
  -- 1.12. def:one-to-one, from 1.8, 1.11
  have s1_12 : Set.MapsTo f (Set.Icc (1 : ℤ) N : Set ℤ) ((Set.Icc (1 : ℤ) (r - 1) : Set ℤ) ×ˢ (Set.Icc (1 : ℤ) (s - 1) : Set ℤ)) ∧ Set.InjOn f (Set.Icc (1 : ℤ) N : Set ℤ) := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (Y := (Set.Icc (1 : ℤ) (r - 1) : Set ℤ) ×ˢ (Set.Icc (1 : ℤ) (s - 1) : Set ℤ)) (f := f) s1_8)).mpr ⟨s1_8, by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_11⟩
  -- 1.13. mun:range-finite a := 1, b := r − 1
  have s1_13 : (Set.Icc (1 : ℤ) (r - 1) : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := r - 1))
  -- 1.14. mun:range-finite a := 1, b := s − 1
  have s1_14 : (Set.Icc (1 : ℤ) (s - 1) : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := s - 1))
  -- 1.15. mun:range-size n := r − 1
  have r751_1 : 0 ≤ r - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := r) hH1)
  have s1_15 : ((Set.Icc (1 : ℤ) (r - 1) : Set ℤ).ncard : ℤ) = r - 1 := by exact (Parley.Items.Stdlib.Counting.mun_range_size (n := r - 1) r751_1)
  -- 1.16. mun:range-size n := s − 1
  have r755_1 : 0 ≤ s - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := s) hH2)
  have s1_16 : ((Set.Icc (1 : ℤ) (s - 1) : Set ℤ).ncard : ℤ) = s - 1 := by exact (Parley.Items.Stdlib.Counting.mun_range_size (n := s - 1) r755_1)
  -- 1.17. calculation
  have s1_17 : N ≤ (r - 1) * (s - 1) := by
    calc N = ((Set.Icc (1 : ℤ) N : Set ℤ).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_range_size (n := N) (le_of_lt hH3)).symm
      _ ≤ (((Set.Icc (1 : ℤ) (r - 1) : Set ℤ) ×ˢ (Set.Icc (1 : ℤ) (s - 1) : Set ℤ)).ncard : ℤ) := by (have h := (Parley.Items.Stdlib.Counting.thm_pigeonhole (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (Y := (Set.Icc (1 : ℤ) (r - 1) : Set ℤ) ×ˢ (Set.Icc (1 : ℤ) (s - 1) : Set ℤ)) (f := f) s1_12); simp only [← Set.Finite.cast_ncard_eq ((Set.finite_Icc _ _ : ((Set.Icc (1 : ℤ) N : Set ℤ) : Set ℤ).Finite)), ← Set.Finite.cast_ncard_eq (((s1_13).prod (s1_14) : ((Set.Icc (1 : ℤ) (r - 1) : Set ℤ) ×ˢ (Set.Icc (1 : ℤ) (s - 1) : Set ℤ) : Set (ℤ × ℤ)).Finite))] at h ⊢; exact_mod_cast h)
      _ = ((Set.Icc (1 : ℤ) (r - 1) : Set ℤ).ncard : ℤ) * ((Set.Icc (1 : ℤ) (s - 1) : Set ℤ).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_product (X := (Set.Icc (1 : ℤ) (r - 1) : Set ℤ)) (Y := (Set.Icc (1 : ℤ) (s - 1) : Set ℤ)) s1_13 s1_14)
      _ = (r - 1) * ((Set.Icc (1 : ℤ) (s - 1) : Set ℤ).ncard : ℤ) := by
          have e_nat : (Set.Icc (1 : ℤ) (r - 1) : Set ℤ).ncard = (r - 1).toNat := by (have h := s1_15; omega)
          have e_w : ((Set.Icc (1 : ℤ) (r - 1) : Set ℤ).ncard : ℤ) = r - 1 := by have h := congrArg (fun x : ℕ => (x : ℤ)) e_nat; push_cast at h ⊢; linear_combination h
          exact congrArg (fun t : ℤ => t * ((Set.Icc (1 : ℤ) (s - 1) : Set ℤ).ncard : ℤ)) e_w
      _ = (r - 1) * (s - 1) := by
          have e_nat : (Set.Icc (1 : ℤ) (s - 1) : Set ℤ).ncard = (s - 1).toNat := by (have h := s1_16; omega)
          have e_w : ((Set.Icc (1 : ℤ) (s - 1) : Set ℤ).ncard : ℤ) = s - 1 := by have h := congrArg (fun x : ℕ => (x : ℤ)) e_nat; push_cast at h ⊢; linear_combination h
          exact congrArg (fun t : ℤ => (r - 1) * t) e_w
  -- 1.18. inequalities, from 1.17
  have s1_18 : ¬ (r - 1) * (s - 1) < N := by linarith only [s1_17]
  exact s1_18 hH5

end Parley.Proofs.Wiedijk.ErdosSzekeres.ErdosSzekeres

module

public import AlgebraTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Proofs.Wiedijk.PrimeFactorisation
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/prime-factorisation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PrimeFactorisation.PrimeTimesProduct

set_option maxHeartbeats 800000 in
theorem prime_times_product (p : ℕ) (hH1 : 0 < p) (hH2 : Nat.Prime p) (r : ℕ) (hH3 : 0 < r) (hH4 : ∃ k : ℕ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) (k : ℤ) : Set ℤ) {n : ℤ | 0 < n} ∧ ((r : ℤ) = (∏ i ∈ Finset.Icc (1 : ℤ) (k : ℤ), (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 (k : ℤ) → Nat.Prime (f i).toNat)))) :
    (∃ k : ℕ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) (k : ℤ) : Set ℤ) {n : ℤ | 0 < n} ∧ ((p : ℤ) * (r : ℤ) = (∏ i ∈ Finset.Icc (1 : ℤ) (k : ℤ), (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 (k : ℤ) → Nat.Prime (f i).toNat)))) := by
  -- 1. D1, from H4
  have s1 : ∃ k : ℕ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) (k : ℤ) : Set ℤ) {n : ℤ | 0 < n} ∧ ((r : ℤ) = (∏ i ∈ Finset.Icc (1 : ℤ) (k : ℤ), (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 (k : ℤ) → Nat.Prime (f i).toNat))) := by parley_set_side
  -- 2. obtain j, g from line 1
  obtain ⟨j, s2a, g, s2b, ⟨s2c, s2d⟩⟩ := s1
  try lift j to ℕ using le_of_lt s2a
  set h : ℤ → ℤ := fun i => @ite _ (i ≤ (j : ℤ)) (Classical.propDecidable (i ≤ (j : ℤ))) (g i) (p : ℤ) with hD2
  -- 3. proof
  have s3 : ∀ i : ℤ, i ∈ Finset.Icc 1 (j : ℤ) → h i = g i := by
    intro i hK1
    try push_cast at hK1
    try have hK1_bounds := Finset.mem_Icc.mp hK1
    -- 3.1. mun:range-bounds a := 1, b := j, k := i, from K1
    have s3_1 : i ≤ (j : ℤ) := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (j : ℤ)) (k := i) hK1)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (j : ℤ)) (k := i) hK1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (j : ℤ)) (k := i) hK1) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (j : ℤ)) (k := i) hK1); parley_set_side)
    -- 3.2. D2, from 3.1
    have r49_1 : i ∈ Finset.Icc (1 : ℤ) ((j : ℤ) + 1) := by first | exact (Parley.Items.Stdlib.Sums.mun_range_extended (a := (1 : ℤ)) (b := (j : ℤ)) (k := i) hK1) | exact ((Parley.Items.Stdlib.Sums.mun_range_extended (a := (1 : ℤ)) (b := (j : ℤ)) (k := i) hK1)).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_extended (a := (1 : ℤ)) (b := (j : ℤ)) (k := i) hK1) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_extended (a := (1 : ℤ)) (b := (j : ℤ)) (k := i) hK1) | (have h := (Parley.Items.Stdlib.Sums.mun_range_extended (a := (1 : ℤ)) (b := (j : ℤ)) (k := i) hK1); parley_set_side)
    have s3_2 : h i = g i := by parley_set_side
    all_goals exact s3_2
  -- 4. proof
  have s4 : ∀ i : ℤ, i ∈ Finset.Icc 1 ((j : ℤ) + 1) → Nat.Prime (h i).toNat := by
    intro i hK2
    try push_cast at hK2
    try have hK2_bounds := Finset.mem_Icc.mp hK2
    -- 4.1. axi:excluded-middle P := i ≤ j
    have s4_1 : i ≤ (j : ℤ) ∨ ¬ i ≤ (j : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ (j : ℤ))) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ (j : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ (j : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ (j : ℤ))) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ (j : ℤ))); parley_set_side)
    -- 4.2. cases, from 4.1
    have s4_2 : Nat.Prime (h i).toNat := by
      rcases s4_1 with hC1 | hC2
      · skip
        -- 4.2.1. D2, from C1, K2
        have s4_2_1 : h i = g i := by parley_set_side
        -- 4.2.2. def:range-between k := i, a := 1, b := j, from C1
        have r69_1 : 1 ≤ i := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (j : ℤ) + 1) (k := i) hK2)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (j : ℤ) + 1) (k := i) hK2); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (j : ℤ) + 1) (k := i) hK2) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (j : ℤ) + 1) (k := i) hK2); parley_set_side)
        have s4_2_2 : i ∈ Finset.Icc (1 : ℤ) (j : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := (j : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := (j : ℤ)))).mpr (by parley_set_side); parley_set_side)
        -- 4.2.3. instantiate i := i in line 2, from 4.2.2
        have s4_2_3 : Nat.Prime (g i).toNat := by first | exact (s2d i (by parley_set_side)) | exact ((s2d i (by parley_set_side))).symm | simpa using (s2d i (by parley_set_side)) | exact_mod_cast (s2d i (by parley_set_side)) | (have h := (s2d i (by parley_set_side)); parley_set_side)
        -- 4.2.4. substitute h(i) = g(i) (line 4.2.1) into line 4.2.3
        have s4_2_4 : Nat.Prime (h i).toNat := by parley_subst_at s4_2_1 s4_2_3
        all_goals parley_set_side
      · skip
        -- 4.2.5. D2, from C2, K2
        have s4_2_5 : h i = (p : ℤ) := by parley_set_side
        -- 4.2.6. substitute h(i) = p (line 4.2.5) into H2
        have s4_2_6 : Nat.Prime (h i).toNat := by parley_subst_at s4_2_5 hH2
        all_goals parley_set_side
    all_goals exact s4_2
  -- 5. proof
  have s5 : ∀ i : ℤ, i ∈ Finset.Icc 1 ((j : ℤ) + 1) → 0 < h i := by
    intro i hK3
    try push_cast at hK3
    try have hK3_bounds := Finset.mem_Icc.mp hK3
    -- 5.1. axi:excluded-middle P := i ≤ j
    have s5_1 : i ≤ (j : ℤ) ∨ ¬ i ≤ (j : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ (j : ℤ))) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ (j : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ (j : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ (j : ℤ))) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ (j : ℤ))); parley_set_side)
    -- 5.2. cases, from 5.1
    have s5_2 : 0 < h i := by
      rcases s5_1 with hC3 | hC4
      · skip
        -- 5.2.1. D2, from C3, K3
        have s5_2_1 : h i = g i := by parley_set_side
        -- 5.2.2. def:range-between k := i, a := 1, b := j, from C3
        have r104_1 : 1 ≤ i := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (j : ℤ) + 1) (k := i) hK3)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (j : ℤ) + 1) (k := i) hK3); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (j : ℤ) + 1) (k := i) hK3) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (j : ℤ) + 1) (k := i) hK3); parley_set_side)
        have s5_2_2 : i ∈ Finset.Icc (1 : ℤ) (j : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := (j : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := (j : ℤ)))).mpr (by parley_set_side); parley_set_side)
        -- 5.2.3. mun:function-value f := g, from 5.2.2
        have s5_2_3 : 0 < g i := by first | exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) (j : ℤ) : Set ℤ)) (E := {n : ℤ | 0 < n}) (f := g) (x := i) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) (j : ℤ) : Set ℤ)) (E := {n : ℤ | 0 < n}) (f := g) (x := i) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) (j : ℤ) : Set ℤ)) (E := {n : ℤ | 0 < n}) (f := g) (x := i) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) (j : ℤ) : Set ℤ)) (E := {n : ℤ | 0 < n}) (f := g) (x := i) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) (j : ℤ) : Set ℤ)) (E := {n : ℤ | 0 < n}) (f := g) (x := i) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
        -- 5.2.4. substitute h(i) = g(i) (line 5.2.1) into line 5.2.3
        have s5_2_4 : 0 < h i := by parley_subst_at s5_2_1 s5_2_3
        all_goals parley_set_side
      · skip
        -- 5.2.5. D2, from C4, K3
        have s5_2_5 : h i = (p : ℤ) := by parley_set_side
        -- 5.2.6. substitute h(i) = p (line 5.2.5) into H1
        have s5_2_6 : 0 < h i := by parley_subst_at s5_2_5 hH1
        all_goals parley_set_side
    all_goals exact s5_2
  -- 6. mun:function-into, from 5
  have s6 : Set.MapsTo h (Set.Icc (1 : ℤ) ((j : ℤ) + 1) : Set ℤ) {n : ℤ | 0 < n} := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (1 : ℤ) ((j : ℤ) + 1) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (1 : ℤ) ((j : ℤ) + 1) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (1 : ℤ) ((j : ℤ) + 1) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (1 : ℤ) ((j : ℤ) + 1) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (1 : ℤ) ((j : ℤ) + 1) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 7. mun:product-termwise a := 1, b := j, t := h, u := g, from 3
  have r127_1 : Set.MapsTo h (Set.Icc (1 : ℤ) ((j : ℤ) + 1) : Set ℤ) {n : ℤ | 0 < n} := by parley_set_side
  have s7 : (∏ i ∈ Finset.Icc (1 : ℤ) (j : ℤ), (h i : ℤ)) = (∏ i ∈ Finset.Icc (1 : ℤ) (j : ℤ), (g i : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_termwise (t := h) (u := g) (X := (Set.univ : Set ℤ)) (Z := Set.univ) (Y := (Set.univ : Set ℤ)) (W := Set.univ) (a := (1 : ℤ)) (b := (j : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_product_termwise (t := h) (u := g) (X := (Set.univ : Set ℤ)) (Z := Set.univ) (Y := (Set.univ : Set ℤ)) (W := Set.univ) (a := (1 : ℤ)) (b := (j : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_termwise (t := h) (u := g) (X := (Set.univ : Set ℤ)) (Z := Set.univ) (Y := (Set.univ : Set ℤ)) (W := Set.univ) (a := (1 : ℤ)) (b := (j : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_termwise (t := h) (u := g) (X := (Set.univ : Set ℤ)) (Z := Set.univ) (Y := (Set.univ : Set ℤ)) (W := Set.univ) (a := (1 : ℤ)) (b := (j : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_termwise (t := h) (u := g) (X := (Set.univ : Set ℤ)) (Z := Set.univ) (Y := (Set.univ : Set ℤ)) (W := Set.univ) (a := (1 : ℤ)) (b := (j : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_termwise (t := h) (u := g) (X := (Set.univ : Set ℤ)) (Z := Set.univ) (Y := (Set.univ : Set ℤ)) (W := Set.univ) (a := (1 : ℤ)) (b := (j : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_termwise (t := h) (u := g) (X := (Set.univ : Set ℤ)) (Z := Set.univ) (Y := (Set.univ : Set ℤ)) (W := Set.univ) (a := (1 : ℤ)) (b := (j : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_termwise (t := h) (u := g) (X := (Set.univ : Set ℤ)) (Z := Set.univ) (Y := (Set.univ : Set ℤ)) (W := Set.univ) (a := (1 : ℤ)) (b := (j : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_termwise (t := h) (u := g) (X := (Set.univ : Set ℤ)) (Z := Set.univ) (Y := (Set.univ : Set ℤ)) (W := Set.univ) (a := (1 : ℤ)) (b := (j : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 8. inequalities
  have s8 : ¬ (j : ℤ) + 1 ≤ (j : ℤ) := by parley_set_side
  -- 9. def:range-between k := j + 1, a := 1, b := j + 1
  have r134_1 : 1 ≤ (j : ℤ) + 1 := by parley_order
  have r134_2 : (j : ℤ) + 1 ≤ (j : ℤ) + 1 := by parley_order
  have s9 : (j : ℤ) + 1 ∈ Finset.Icc (1 : ℤ) ((j : ℤ) + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := (j : ℤ) + 1) (a := (1 : ℤ)) (b := (j : ℤ) + 1))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := (j : ℤ) + 1) (a := (1 : ℤ)) (b := (j : ℤ) + 1))).mpr (by parley_set_side); parley_set_side)
  -- 10. D2, from 8, 9
  have s10 : h ((j : ℤ) + 1) = (p : ℤ) := by parley_set_side
  -- 11. substitute r = ∏(i ∈ {1, …, j}) g(i) (line 2)
  have s11 : (∏ i ∈ Finset.Icc (1 : ℤ) (j : ℤ), (g i : ℤ)) * h ((j : ℤ) + 1) = (r : ℤ) * h ((j : ℤ) + 1) := by parley_subst s2c
  -- 12. calculation
  have r145_1 : (j : ℤ) ≥ 1 := by parley_set_side
  have s12 : (p : ℤ) * (r : ℤ) = (∏ i ∈ Finset.Icc (1 : ℤ) ((j : ℤ) + 1), (h i : ℤ)) := by
    calc (p : ℤ) * (r : ℤ) = (r : ℤ) * (p : ℤ) := by parley_ring
      _ = (r : ℤ) * h ((j : ℤ) + 1) := by parley_subst s10
      _ = (∏ i ∈ Finset.Icc (1 : ℤ) (j : ℤ), (g i : ℤ)) * h ((j : ℤ) + 1) := by parley_set_side
      _ = (∏ i ∈ Finset.Icc (1 : ℤ) (j : ℤ), (h i : ℤ)) * h ((j : ℤ) + 1) := by parley_subst s7
      _ = (∏ i ∈ Finset.Icc (1 : ℤ) ((j : ℤ) + 1), (h i : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_extended (t := h) (a := (1 : ℤ)) (n := (j : ℤ)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := h) (a := (1 : ℤ)) (n := (j : ℤ)) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := h) (a := (1 : ℤ)) (n := (j : ℤ)) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_extended (t := h) (a := (1 : ℤ)) (n := (j : ℤ)) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_extended (t := h) (a := (1 : ℤ)) (n := (j : ℤ)) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := h) (a := (1 : ℤ)) (n := (j : ℤ)) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := h) (a := (1 : ℤ)) (n := (j : ℤ)) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := h) (a := (1 : ℤ)) (n := (j : ℤ)) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := h) (a := (1 : ℤ)) (n := (j : ℤ)) (by parley_set_side)); parley_set_side)
  -- 13. exhibit, from 4, 6, 12
  have s13 : ∃ k : ℕ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) (k : ℤ) : Set ℤ) {n : ℤ | 0 < n} ∧ ((p : ℤ) * (r : ℤ) = (∏ i ∈ Finset.Icc (1 : ℤ) (k : ℤ), (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 (k : ℤ) → Nat.Prime (f i).toNat))) := ⟨j + 1, by parley_set_side, h, by parley_set_side, ⟨by parley_set_side, by parley_set_side⟩⟩
  -- 14. D1, from 13
  have s14 : ∃ k : ℕ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) (k : ℤ) : Set ℤ) {n : ℤ | 0 < n} ∧ ((p : ℤ) * (r : ℤ) = (∏ i ∈ Finset.Icc (1 : ℤ) (k : ℤ), (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 (k : ℤ) → Nat.Prime (f i).toNat))) := by parley_set_side
  all_goals exact s14

end Parley.Proofs.Wiedijk.PrimeFactorisation.PrimeTimesProduct

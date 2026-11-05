module

public import ArithTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-definition-folded-without-its-pair.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefinitionFoldedWithoutItsPair.ADefinitionFoldedWithoutItsPair

set_option maxHeartbeats 1200000 in
theorem a_definition_folded_without_its_pair (g : ℝ → ℝ) (hD2 : ∀ x : ℝ, x ∈ {y : ℝ | y > 0} → g x = Real.sqrt x) :
    ContinuousOn g {y : ℝ | y > 0} := by
  set D : Set ℝ := {y : ℝ | y > 0} with hD1
  -- 1. mun:set-builder-subset, from D1
  have s1 : D ⊆ (Set.univ : Set ℝ) := by
    try simp only [hD1] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ))); parley_set_side)
  -- 2. proof
  have s2 : ∀ x ∈ D, True := by
    intro x hK1
    -- 2.1. def:set-builder, from D1, K1
    have s2_1 : x > 0 := by
      try simp only [hD1] at *
      try push_cast at *
      first | linarith [(((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := x))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := x))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := x))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := x))).mp (by parley_set_side)).2; parley_set_side)
    -- 2.2. inequalities
    have s2_2 : x ≥ 0 := by parley_order
    -- 2.3. def:sqrt, from 2.1, 2.2
    have s2_3a : Real.sqrt x ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_set_side)); parley_set_side)
    have s2_3b : Real.sqrt x ^ 2 = x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); parley_set_side)
    -- 2.4. D2, from K1
    have s2_4 : g x = Real.sqrt x := by (try simp only [hD2]); first | done | parley_set_side
    -- 2.5. substitute g(x) = √x (line 2.4) into line 2.3
    all_goals parley_set_side
  -- 3. mun:function-into, from 2
  have s3 : Set.MapsTo g D (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := D) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := D) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := D) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := D) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := D) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 4. proof
  have s4 : ∀ c ∈ D, ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, abs (x - c) < δ → abs (g x - g c) < ε)) := by
    intro c hK2
    intro ε
    intro hA1
    -- 4.1. def:set-builder, from D1, K2
    have s4_1 : c > 0 := by
      try simp only [hD1] at *
      try push_cast at *
      first | linarith [(((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := c))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := c))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := c))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := c))).mp (by parley_set_side)).2; parley_set_side)
    -- 4.2. inequalities
    have s4_2 : c ≥ 0 := by parley_order
    -- 4.3. def:sqrt x := c, from 4.1, 4.2
    have s4_3a : Real.sqrt c ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := c) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := c) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := c) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := c) (by parley_set_side)); parley_set_side)
    have s4_3b : Real.sqrt c ^ 2 = c := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := c) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := c) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := c) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := c) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := c) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := c) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := c) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := c) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := c) (by parley_set_side)); parley_set_side)
    -- 4.4. contradiction
    have s4_4 : Real.sqrt c > 0 := by
      by_contra hc_hS1
      have hS1 : ¬ Real.sqrt c > 0 := by parley_suppose hc_hS1
      -- 4.4.1. inequalities, from S1, 4.3
      have s4_4_1 : Real.sqrt c ≤ 0 := by parley_order
      -- 4.4.2. inequalities, from 4.3
      have s4_4_2 : Real.sqrt c ≥ 0 := by parley_order
      -- 4.4.3. antisymmetry, from 4.4.1, 4.4.2
      have s4_4_3 : Real.sqrt c = 0 := by parley_set_side
      -- 4.4.4. substitute √c = 0 (line 4.4.3)
      have s4_4_4 : Real.sqrt c ^ 2 = 0 ^ 2 := by parley_subst s4_4_3
      -- 4.4.5. arithmetic
      have s4_4_5 : (0 ^ 2 : ℝ) = 0 := by parley_arith
      -- 4.4.6. calculation
      have s4_4_6 : c = 0 := by
        calc c = Real.sqrt c ^ 2 := by parley_set_side
          _ = 0 ^ 2 := by parley_set_side
          _ = 0 := by parley_set_side
      -- 4.4.7. inequalities
      have s4_4_7 : c ≤ 0 := by parley_order
      -- 4.4.8. inequalities, from 4.4.7
      have s4_4_8 : ¬ c > 0 := by parley_set_side
      all_goals parley_set_side
    -- 4.5. mun:less-scaled x := 0, y := √c, c := ε, from A1, 4.3, 4.4
    have s4_5 : ε * 0 < ε * Real.sqrt c := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (0 : ℝ)) (y := Real.sqrt c) (c := ε) (by parley_set_side))).mp (by parley_set_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (0 : ℝ)) (y := Real.sqrt c) (c := ε) (by parley_set_side))).mp (by parley_set_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (0 : ℝ)) (y := Real.sqrt c) (c := ε) (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (0 : ℝ)) (y := Real.sqrt c) (c := ε) (by parley_set_side))).mp (by parley_set_side); parley_set_side)
    -- 4.6. membership, from 4.3
    -- 4.7. inequalities, from 4.3, 4.5
    have s4_7 : ε * Real.sqrt c > 0 := by parley_order
    -- 4.8. proof
    have s4_8 : ∀ x ∈ D, abs (x - c) < ε * Real.sqrt c → abs (g x - g c) < ε := by
      intro x hK4
      intro hA2
      -- 4.8.1. def:set-builder, from D1, K4
      have s4_8_1 : x > 0 := by
        try simp only [hD1] at *
        try push_cast at *
        first | linarith [(((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := x))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := x))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := x))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => 0 < y)) (X := (Set.univ : Set ℝ)) (u := x))).mp (by parley_set_side)).2; parley_set_side)
      -- 4.8.2. inequalities
      have s4_8_2 : x ≥ 0 := by parley_order
      -- 4.8.3. def:sqrt, from 4.8.1, 4.8.2
      have s4_8_3a : Real.sqrt x ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_set_side)); parley_set_side)
      have s4_8_3b : Real.sqrt x ^ 2 = x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_set_side)); parley_set_side)
      -- 4.8.4. membership, from 4.1, 4.8.1
      -- 4.8.5. mun:abs-real x := x − c, from 4.8.4
      -- 4.8.6. membership, from 4.3, 4.8.3
      -- 4.8.7. mun:abs-real x := √x − √c, from 4.8.6
      -- 4.8.8. D2, from K4
      have s4_8_8 : g x = Real.sqrt x := by (try simp only [hD2]); first | done | parley_set_side
      -- 4.8.9. D2, from K2
      have s4_8_9 : g c = Real.sqrt c := by (try simp only [hD2]); first | done | parley_set_side
      -- 4.8.10. algebra, from 4.3, 4.8.3
      have s4_8_10 : (Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c) = x - c := by linear_combination (norm := parley_norm) (-1) * s4_3b + s4_8_3b
      -- 4.8.11. inequalities, from 4.3, 4.8.3
      have s4_8_11 : Real.sqrt x + Real.sqrt c ≥ 0 := by parley_order
      -- 4.8.12. mun:abs-nonneg x := √x − √c, from 4.8.6
      have s4_8_12 : abs (Real.sqrt x - Real.sqrt c) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (Real.sqrt x : ℂ) - (Real.sqrt c : ℂ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (Real.sqrt x : ℂ) - (Real.sqrt c : ℂ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (Real.sqrt x : ℂ) - (Real.sqrt c : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (Real.sqrt x : ℂ) - (Real.sqrt c : ℂ))); parley_set_side)
      -- 4.8.13. def:abs x := √x + √c, from 4.8.11
      have s4_8_13 : abs (Real.sqrt x + Real.sqrt c) = Real.sqrt x + Real.sqrt c := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := Real.sqrt x + Real.sqrt c)) (by parley_set_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := Real.sqrt x + Real.sqrt c)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := Real.sqrt x + Real.sqrt c)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := Real.sqrt x + Real.sqrt c)) (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := Real.sqrt x + Real.sqrt c)) (by parley_set_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := Real.sqrt x + Real.sqrt c)) (by parley_set_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := Real.sqrt x + Real.sqrt c)) (by parley_set_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := Real.sqrt x + Real.sqrt c)) (by parley_set_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := Real.sqrt x + Real.sqrt c)) (by parley_set_side); parley_set_side)
      -- 4.8.14. substitute (√x − √c)·(√x + √c) = x − c (line 4.8.10)
      have s4_8_14 : abs (x - c) = abs ((Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c)) := by parley_subst s4_8_10
      -- 4.8.15. mun:abs-product x := √x − √c, y := √x + √c, from 4.8.6
      have s4_8_15 : abs ((Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c)) = abs (Real.sqrt x - Real.sqrt c) * abs (Real.sqrt x + Real.sqrt c) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_product (x := Real.sqrt x - Real.sqrt c) (y := Real.sqrt x + Real.sqrt c)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := Real.sqrt x - Real.sqrt c) (y := Real.sqrt x + Real.sqrt c)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := Real.sqrt x - Real.sqrt c) (y := Real.sqrt x + Real.sqrt c)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_product (x := Real.sqrt x - Real.sqrt c) (y := Real.sqrt x + Real.sqrt c)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_product (x := Real.sqrt x - Real.sqrt c) (y := Real.sqrt x + Real.sqrt c))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := Real.sqrt x - Real.sqrt c) (y := Real.sqrt x + Real.sqrt c)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := Real.sqrt x - Real.sqrt c) (y := Real.sqrt x + Real.sqrt c)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := Real.sqrt x - Real.sqrt c) (y := Real.sqrt x + Real.sqrt c)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := Real.sqrt x - Real.sqrt c) (y := Real.sqrt x + Real.sqrt c)); parley_set_side)
      -- 4.8.16. substitute |√x + √c| = √x + √c (line 4.8.13)
      have s4_8_16 : abs (Real.sqrt x - Real.sqrt c) * abs (Real.sqrt x + Real.sqrt c) = abs (Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c) := by parley_subst s4_8_13
      -- 4.8.17. calculation
      have s4_8_17 : abs (x - c) = abs (Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c) := by
        calc abs (x - c) = abs ((Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c)) := by parley_set_side
          _ = abs (Real.sqrt x - Real.sqrt c) * abs (Real.sqrt x + Real.sqrt c) := by parley_set_side
          _ = abs (Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c) := by parley_set_side
      -- 4.8.18. mun:product-nonneg x := |√x − √c|, y := √x, from 4.8.3, 4.8.7, 4.8.12
      have s4_8_18 : abs (Real.sqrt x - Real.sqrt c) * Real.sqrt x ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := abs (Real.sqrt x - Real.sqrt c)) (y := Real.sqrt x) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := abs (Real.sqrt x - Real.sqrt c)) (y := Real.sqrt x) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := abs (Real.sqrt x - Real.sqrt c)) (y := Real.sqrt x) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := abs (Real.sqrt x - Real.sqrt c)) (y := Real.sqrt x) (by parley_set_side) (by parley_set_side)); parley_set_side)
      -- 4.8.19. algebra, from 4.3, 4.8.3
      have s4_8_19 : abs (Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c) = abs (Real.sqrt x - Real.sqrt c) * Real.sqrt x + Real.sqrt c * abs (Real.sqrt x - Real.sqrt c) := by linear_combination (norm := parley_norm) 0
      -- 4.8.20. inequalities
      have s4_8_20 : abs (Real.sqrt x - Real.sqrt c) * Real.sqrt x + Real.sqrt c * abs (Real.sqrt x - Real.sqrt c) ≥ Real.sqrt c * abs (Real.sqrt x - Real.sqrt c) := by parley_order
      -- 4.8.21. transitivity, from 4.8.20, 4.8.19, 4.8.17
      have s4_8_21 : Real.sqrt c * abs (Real.sqrt x - Real.sqrt c) ≤ abs (x - c) := by parley_order
      -- 4.8.22. algebra, from 4.3
      have s4_8_22 : ε * Real.sqrt c = Real.sqrt c * ε := by linear_combination (norm := parley_norm) 0
      -- 4.8.23. transitivity, from 4.8.21, A2, 4.8.22
      have s4_8_23 : Real.sqrt c * abs (Real.sqrt x - Real.sqrt c) < Real.sqrt c * ε := by parley_order
      -- 4.8.24. mun:less-scaled x := |√x − √c|, y := ε, c := √c, from 4.3, 4.4, 4.8.7, 4.8.23
      have s4_8_24 : abs (Real.sqrt x - Real.sqrt c) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs (Real.sqrt x - Real.sqrt c)) (y := ε) (c := Real.sqrt c) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs (Real.sqrt x - Real.sqrt c)) (y := ε) (c := Real.sqrt c) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
      -- 4.8.25. substitute g(x) = √x (line 4.8.8) into line 4.8.24
      have s4_8_25 : abs (g x - Real.sqrt c) < ε := by parley_subst_at s4_8_8 s4_8_24
      -- 4.8.26. substitute g(c) = √c (line 4.8.9) into line 4.8.25
      have s4_8_26 : abs (g x - g c) < ε := by parley_subst_at s4_8_9 s4_8_25
      all_goals parley_set_side
    -- 4.9. exhibit, from 4.6, 4.7, 4.8
    have s4_9 : ∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, abs (x - c) < δ → abs (g x - g c) < ε) := ⟨ε * Real.sqrt c, ⟨by parley_set_side, by parley_set_side⟩⟩
    all_goals parley_set_side
  -- 5. def:continuous-on, from 1, 4
  have r217_1 : Set.MapsTo g D (Set.univ : Set ℝ) := by parley_set_side
  have s5 : ContinuousOn g D := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_continuous_on (f := g) (D := D) s1)).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_continuous_on (f := g) (D := D) s1)).mpr (by parley_set_side); parley_set_side)
  all_goals parley_set_side

end Parley.Tests.Elaborator.ADefinitionFoldedWithoutItsPair.ADefinitionFoldedWithoutItsPair

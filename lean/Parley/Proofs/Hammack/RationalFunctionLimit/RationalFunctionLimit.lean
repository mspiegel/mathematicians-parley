module

public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/rational-function-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalFunctionLimit.RationalFunctionLimit

theorem rational_function_limit (a : ℤ → ℝ) (hH2 : ∀ n : ℕ, 0 < n → a (n : ℤ) = (5 * (n : ℝ) ^ 2 + (n : ℝ) + 1) / (4 * (n : ℝ) ^ 2 + 2)) :
    Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds (5 / 4)) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - 5 / 4) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. obtain N: thm:archimedean x := ε, from A1
    obtain ⟨N, s1_1a, s1_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε) (by parley_side))
    -- 1.2. proof
    have s1_2 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - 5 / 4) < ε := by
      intro n hK2
      intro hA2
      -- 1.2.1. inequalities, from K2
      have s1_2_1 : (n : ℝ) > 0 := by parley_order
      -- 1.2.2. inequalities, from K2
      have s1_2_2 : (n : ℝ) ≥ 1 := by parley_order
      -- 1.2.3. mun:square-positive x := n
      have r40_1 : (n : ℝ) ≠ 0 := by parley_side
      have s1_2_3 : (n : ℝ) ^ 2 > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_positive (x := (n : ℝ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := (n : ℝ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_positive (x := (n : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := (n : ℝ)) (by parley_side)); parley_side)
      -- 1.2.4. inequalities
      have s1_2_4 : 4 * (n : ℝ) ^ 2 > 0 := by parley_order
      -- 1.2.5. inequalities, from 1.2.4
      have s1_2_5 : 4 * (n : ℝ) ^ 2 + 2 > 0 := by parley_order
      -- 1.2.6. inequalities
      have s1_2_6 : 8 * (n : ℝ) ^ 2 + 4 > 0 := by parley_order
      -- 1.2.7. mun:product-positive x := n, y := 8n² + 4, from 1.2.1, 1.2.6
      have s1_2_7 : (n : ℝ) * (8 * (n : ℝ) ^ 2 + 4) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_positive (x := (n : ℝ)) (y := 8 * (n : ℝ) ^ 2 + 4) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (n : ℝ)) (y := 8 * (n : ℝ) ^ 2 + 4) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (n : ℝ)) (y := 8 * (n : ℝ) ^ 2 + 4) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (n : ℝ)) (y := 8 * (n : ℝ) ^ 2 + 4) (by parley_side) (by parley_side)); parley_side)
      -- 1.2.8. algebra, from H2
      have s1_2_8 : a (n : ℤ) - 5 / 4 = (2 * (n : ℝ) - 3) / (8 * (n : ℝ) ^ 2 + 4) := by linear_combination (norm := parley_field) ((4) / ((4))) * (hH2 n (by parley_side))
      -- 1.2.9. algebra
      have s1_2_9 : 1 / (n : ℝ) - (2 * (n : ℝ) - 3) / (8 * (n : ℝ) ^ 2 + 4) = (6 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 4) / ((n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) := by parley_ring
      -- 1.2.10. inequalities
      have s1_2_10 : 6 * (n : ℝ) ^ 2 > 0 := by parley_order
      -- 1.2.11. inequalities
      have s1_2_11 : 3 * (n : ℝ) > 0 := by parley_order
      -- 1.2.12. inequalities, from 1.2.10, 1.2.11
      have s1_2_12 : 6 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 4 > 0 := by parley_order
      -- 1.2.13. mun:quotient-positive x := 6n² + 3n + 4, y := n·(8n² + 4), from 1.2.7, 1.2.12
      have s1_2_13 : (6 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 4) / ((n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 6 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 4) (y := (n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 6 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 4) (y := (n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 6 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 4) (y := (n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 6 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 4) (y := (n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) (by parley_side) (by parley_side)); parley_side)
      -- 1.2.14. transitivity, from 1.2.13, 1.2.9
      have s1_2_14 : 0 < 1 / (n : ℝ) - (2 * (n : ℝ) - 3) / (8 * (n : ℝ) ^ 2 + 4) := by parley_order
      -- 1.2.15. inequalities
      have s1_2_15 : (2 * (n : ℝ) - 3) / (8 * (n : ℝ) ^ 2 + 4) < 1 / (n : ℝ) := by parley_order
      -- 1.2.16. algebra
      have s1_2_16 : 1 / (n : ℝ) + (2 * (n : ℝ) - 3) / (8 * (n : ℝ) ^ 2 + 4) = (10 * (n : ℝ) ^ 2 - 3 * (n : ℝ) + 4) / ((n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) := by parley_ring
      -- 1.2.17. mun:multiply-le x := 1, y := n, c := n, from 1.2.2
      have r95_1 : (n : ℝ) > 0 := by parley_side
      have s1_2_17 : (n : ℝ) * 1 ≤ (n : ℝ) * (n : ℝ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := (n : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := (n : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := (n : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := (n : ℝ)) (by parley_side) (by parley_side)); parley_side)
      -- 1.2.18. algebra
      have s1_2_18 : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by parley_ring
      -- 1.2.19. transitivity, from 1.2.17, 1.2.18
      have s1_2_19 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by parley_order
      -- 1.2.20. inequalities
      have s1_2_20 : 7 * (n : ℝ) ^ 2 ≤ 10 * (n : ℝ) ^ 2 - 3 * (n : ℝ) := by parley_order
      -- 1.2.21. inequalities
      have s1_2_21 : 7 * (n : ℝ) ^ 2 > 0 := by parley_order
      -- 1.2.22. transitivity, from 1.2.21, 1.2.20
      have s1_2_22 : 0 < 10 * (n : ℝ) ^ 2 - 3 * (n : ℝ) := by parley_order
      -- 1.2.23. mun:quotient-positive x := 10n² − 3n + 4, y := n·(8n² + 4), from 1.2.7
      have r122_1 : 10 * (n : ℝ) ^ 2 - 3 * (n : ℝ) + 4 > 0 := by parley_order
      have s1_2_23 : (10 * (n : ℝ) ^ 2 - 3 * (n : ℝ) + 4) / ((n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 10 * (n : ℝ) ^ 2 - 3 * (n : ℝ) + 4) (y := (n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 10 * (n : ℝ) ^ 2 - 3 * (n : ℝ) + 4) (y := (n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 10 * (n : ℝ) ^ 2 - 3 * (n : ℝ) + 4) (y := (n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 10 * (n : ℝ) ^ 2 - 3 * (n : ℝ) + 4) (y := (n : ℝ) * (8 * (n : ℝ) ^ 2 + 4)) (by parley_side) (by parley_side)); parley_side)
      -- 1.2.24. transitivity, from 1.2.23, 1.2.16
      have s1_2_24 : 0 < 1 / (n : ℝ) + (2 * (n : ℝ) - 3) / (8 * (n : ℝ) ^ 2 + 4) := by parley_order
      -- 1.2.25. inequalities
      have s1_2_25 : -(1 / (n : ℝ)) < (2 * (n : ℝ) - 3) / (8 * (n : ℝ) ^ 2 + 4) := by parley_order
      -- 1.2.26. mun:reciprocal-order x := N, y := n, from A2
      have r135_1 : (N : ℝ) > 0 := by parley_order
      have r135_2 : (n : ℝ) > 0 := by parley_side
      have s1_2_26 : 1 / (n : ℝ) ≤ 1 / (N : ℝ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side); parley_side)
      -- 1.2.27. transitivity, from 1.2.26, 1.1
      have s1_2_27 : 1 / (n : ℝ) < ε := by parley_order
      -- 1.2.28. transitivity, from 1.2.8, 1.2.15, 1.2.27
      have s1_2_28 : a (n : ℤ) - 5 / 4 < ε := by parley_order
      -- 1.2.29. inequalities
      have s1_2_29 : a (n : ℤ) < 5 / 4 + ε := by parley_order
      -- 1.2.30. inequalities
      have s1_2_30 : -ε < -(1 / (n : ℝ)) := by parley_order
      -- 1.2.31. transitivity, from 1.2.30, 1.2.25, 1.2.8
      have s1_2_31 : -ε < a (n : ℤ) - 5 / 4 := by parley_order
      -- 1.2.32. inequalities
      have s1_2_32 : 5 / 4 - ε < a (n : ℤ) := by parley_order
      -- 1.2.33. join 1.2.32, 1.2.29
      have s1_2_33 : 5 / 4 - ε < a (n : ℤ) ∧ a (n : ℤ) < 5 / 4 + ε := by parley_side
      -- 1.2.34. mun:abs-difference-lt x := a(n), c := 5/4, δ := ε, from 1.2.33
      have s1_2_34 : abs (a (n : ℤ) - 5 / 4) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := (5 / 4 : ℝ)) (δ := ε))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := (5 / 4 : ℝ)) (δ := ε))).mpr (by parley_side); parley_side)
      all_goals parley_side
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - 5 / 4) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 2. def:tends-to L := 5/4, from 1
  have s2 : Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds (5 / 4)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (5 / 4 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (5 / 4 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.RationalFunctionLimit.RationalFunctionLimit

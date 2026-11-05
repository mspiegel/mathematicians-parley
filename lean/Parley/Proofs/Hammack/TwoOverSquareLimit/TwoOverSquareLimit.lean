module

public import AlgebraTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/two-over-square-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.TwoOverSquareLimit.TwoOverSquareLimit

set_option maxHeartbeats 400000 in
theorem two_over_square_limit (a : ℤ → ℝ) (hH2 : ∀ n : ℕ, 0 < n → a (n : ℤ) = 5 + 2 / (n : ℝ) ^ 2) :
    Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds 5) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - 5) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. inequalities
    have s1_1 : ε / 2 > 0 := by parley_order
    -- 1.2. obtain N: thm:archimedean x := ε/2, from 1.1
    obtain ⟨N, s1_2a, s1_2b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε / 2) (by parley_side))
    try lift N to ℕ using le_of_lt s1_2a
    -- 1.3. proof
    have s1_3 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - 5) < ε := by
      intro n hK2
      intro hA2
      -- 1.3.1. inequalities, from K2
      have s1_3_1 : (n : ℝ) > 0 := by parley_order
      -- 1.3.2. inequalities, from K2
      have s1_3_2 : (n : ℝ) ≥ 1 := by parley_order
      -- 1.3.3. mun:multiply-le x := 1, y := n, c := n, from 1.3.2
      have r41_1 : (n : ℝ) > 0 := by parley_side
      have s1_3_3 : (n : ℝ) * 1 ≤ (n : ℝ) * (n : ℝ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := (n : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := (n : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := (n : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := (n : ℝ)) (by parley_side) (by parley_side)); parley_side)
      -- 1.3.4. algebra
      have s1_3_4 : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by parley_ring
      -- 1.3.5. transitivity, from 1.3.3, 1.3.4
      have s1_3_5 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by parley_order
      -- 1.3.6. transitivity, from 1.3.1, 1.3.5
      have s1_3_6 : (n : ℝ) ^ 2 > 0 := by parley_order
      -- 1.3.7. mun:reciprocal-order x := n, y := n², from 1.3.5
      have r54_1 : (n : ℝ) > 0 := by parley_side
      have r54_2 : (n : ℝ) ^ 2 > 0 := by parley_side
      have s1_3_7 : 1 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (n : ℝ)) (by parley_side) (y := (n : ℝ) ^ 2) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (n : ℝ)) (by parley_side) (y := (n : ℝ) ^ 2) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (n : ℝ)) (by parley_side) (y := (n : ℝ) ^ 2) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (n : ℝ)) (by parley_side) (y := (n : ℝ) ^ 2) (by parley_side))).mp (by parley_side); parley_side)
      -- 1.3.8. mun:reciprocal-order x := N, y := n, from A2
      have r59_1 : (N : ℝ) > 0 := by parley_order
      have r59_2 : (n : ℝ) > 0 := by parley_side
      have s1_3_8 : 1 / (n : ℝ) ≤ 1 / (N : ℝ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side); parley_side)
      -- 1.3.9. inequalities
      have s1_3_9 : 2 * (1 / (n : ℝ) ^ 2) ≤ 2 * (1 / (n : ℝ)) := by parley_order
      -- 1.3.10. inequalities
      have s1_3_10 : 2 * (1 / (n : ℝ)) ≤ 2 * (1 / (N : ℝ)) := by parley_order
      -- 1.3.11. inequalities
      have s1_3_11 : 2 * (1 / (N : ℝ)) < ε := by parley_order
      -- 1.3.12. algebra, from H2
      have s1_3_12 : a (n : ℤ) - 5 = 2 * (1 / (n : ℝ) ^ 2) := by linear_combination (norm := parley_field) (hH2 n (by parley_side))
      -- 1.3.13. transitivity, from 1.3.12, 1.3.9, 1.3.10, 1.3.11
      have s1_3_13 : a (n : ℤ) - 5 < ε := by parley_order
      -- 1.3.14. mun:reciprocal-positive x := n², from 1.3.6
      have s1_3_14 : 1 / (n : ℝ) ^ 2 > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℝ) ^ 2) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℝ) ^ 2) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℝ) ^ 2) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℝ) ^ 2) (by parley_side)); parley_side)
      -- 1.3.15. inequalities
      have s1_3_15 : 2 * (1 / (n : ℝ) ^ 2) > 0 := by parley_order
      -- 1.3.16. transitivity, from 1.3.15, 1.3.12
      have s1_3_16 : 0 < a (n : ℤ) - 5 := by parley_order
      -- 1.3.17. def:abs x := a(n) − 5
      have r99_2 : 0 ≤ a (n : ℤ) - 5 := by parley_side
      have s1_3_17 : abs (a (n : ℤ) - 5) = a (n : ℤ) - 5 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a (n : ℤ) - 5)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a (n : ℤ) - 5)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a (n : ℤ) - 5)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a (n : ℤ) - 5)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := a (n : ℤ) - 5)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a (n : ℤ) - 5)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a (n : ℤ) - 5)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a (n : ℤ) - 5)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a (n : ℤ) - 5)) (by parley_side); parley_side)
      -- 1.3.18. transitivity, from 1.3.17, 1.3.13
      have s1_3_18 : abs (a (n : ℤ) - 5) < ε := by parley_order
      all_goals parley_side
    -- 1.4. exhibit, from 1.3
    have s1_4 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - 5) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 2. def:tends-to L := 5, from 1
  have s2 : Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds 5) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (5 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (5 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.TwoOverSquareLimit.TwoOverSquareLimit

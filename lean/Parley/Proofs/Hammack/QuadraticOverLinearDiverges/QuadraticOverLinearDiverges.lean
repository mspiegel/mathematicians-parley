module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/quadratic-over-linear-diverges.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.QuadraticOverLinearDiverges.QuadraticOverLinearDiverges

theorem quadratic_over_linear_diverges (a : ℤ → ℝ) (hH2 : ∀ n : ℕ, 0 < n → a (n : ℤ) = (2 * (n : ℝ) ^ 2 + 1) / (3 * (n : ℝ) - 1)) :
    (∀ M : ℝ, ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℤ) > (N : ℤ) → a (n : ℤ) > M)) := by
  -- 1. proof
  have s1 : ∀ M : ℝ, ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℤ) > (N : ℤ) → a (n : ℤ) > M) := by
    intro M
    -- 1.1. obtain N: thm:archimedean-natural x := 3M
    obtain ⟨N, s1_1a, s1_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean_natural (x := 3 * M))
    -- 1.2. proof
    have s1_2 : ∀ n : ℕ, 0 < n → (n : ℤ) > (N : ℤ) → a (n : ℤ) > M := by
      intro n hK2
      intro hA2
      -- 1.2.1. inequalities, from K2
      have s1_2_1 : (n : ℤ) ≥ 1 := by parley_side
      -- 1.2.2. inequalities, from K2
      have s1_2_2 : (n : ℤ) > 0 := by parley_side
      -- 1.2.3. inequalities
      have s1_2_3 : 3 * (n : ℤ) - 1 ≥ 2 := by parley_side
      -- 1.2.4. inequalities, from 1.2.3
      have s1_2_4 : 3 * (n : ℤ) - 1 > 0 := by parley_side
      -- 1.2.5. inequalities
      have s1_2_5 : 3 * (n : ℤ) - 1 ≠ 0 := by parley_side
      -- 1.2.6. inequalities
      have s1_2_6 : (n : ℚ) ^ 2 - (n : ℚ) / 3 < (n : ℚ) ^ 2 := by parley_side
      -- 1.2.7. mun:square-nonneg x := n
      have s1_2_7 : (n : ℤ) ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := (n : ℤ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := (n : ℤ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := (n : ℤ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := (n : ℤ))); parley_side)
      -- 1.2.8. inequalities, from 1.2.7
      have s1_2_8 : 0 < (n : ℤ) ^ 2 + 1 := by parley_side
      -- 1.2.9. inequalities
      have s1_2_9 : (n : ℤ) ^ 2 < 2 * (n : ℤ) ^ 2 + 1 := by parley_side
      -- 1.2.10. calculation
      have r64_1 : 3 * (n : ℤ) - 1 ≠ 0 := by parley_side
      have s1_2_10 : (3 * (n : ℝ) - 1) * ((n : ℝ) / 3) < (3 * (n : ℝ) - 1) * a (n : ℤ) := by
        calc (3 * (n : ℝ) - 1) * ((n : ℝ) / 3) = (n : ℝ) ^ 2 - (n : ℝ) / 3 := by parley_ring
          _ < (n : ℝ) ^ 2 := by parley_side
          _ < 2 * (n : ℝ) ^ 2 + 1 := by parley_side
          _ = (3 * (n : ℝ) - 1) * a (n : ℤ) := by linear_combination (norm := parley_field) (-3 * (n : ℝ) + 1) * (hH2 n (by parley_side))
      -- 1.2.11. mun:less-scaled x := n/3, y := a(n), c := 3n − 1, from 1.2.4, 1.2.10
      have s1_2_11 : (n : ℝ) / 3 < a (n : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (n : ℝ) / 3) (y := a (n : ℤ)) (c := 3 * (n : ℝ) - 1) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (n : ℝ) / 3) (y := a (n : ℤ)) (c := 3 * (n : ℝ) - 1) (by parley_side))).mpr (by parley_side); parley_side)
      -- 1.2.12. transitivity, from 1.1, A2
      have s1_2_12 : 3 * M < (n : ℝ) := by parley_side
      -- 1.2.13. inequalities
      have s1_2_13 : M < (n : ℝ) / 3 := by parley_side
      -- 1.2.14. transitivity, from 1.2.13, 1.2.11
      have s1_2_14 : a (n : ℤ) > M := by parley_side
      all_goals parley_side
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℤ) > (N : ℤ) → a (n : ℤ) > M) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.QuadraticOverLinearDiverges.QuadraticOverLinearDiverges

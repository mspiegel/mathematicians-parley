module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/rational-sequence-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSequenceLimit.RationalSequenceLimit

theorem rational_sequence_limit (a : ℤ → ℝ) (hH2 : ∀ n : ℕ, 0 < n → a (n : ℤ) = (2 * (n : ℝ) + 1) / (3 * (n : ℝ) - 1)) :
    Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds (2 / 3)) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - 2 / 3) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. obtain N: thm:archimedean x := ε, from A1
    obtain ⟨N, s1_1a, s1_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε) (by parley_side))
    try lift N to ℕ using le_of_lt s1_1a
    -- 1.2. proof
    have s1_2 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - 2 / 3) < ε := by
      intro n hK2
      intro hA2
      -- 1.2.1. inequalities, from K2
      have s1_2_1 : (n : ℝ) ≥ 1 := by parley_order
      -- 1.2.2. inequalities, from K2
      have s1_2_2 : (n : ℝ) > 0 := by parley_order
      -- 1.2.3. inequalities
      have s1_2_3 : 3 * (n : ℝ) - 1 ≥ 2 := by parley_order
      -- 1.2.4. inequalities, from 1.2.3
      have s1_2_4 : 3 * (n : ℝ) - 1 > 0 := by parley_order
      -- 1.2.5. inequalities
      have s1_2_5 : 9 * (n : ℝ) - 3 ≥ 5 * (n : ℝ) + 1 := by parley_order
      -- 1.2.6. inequalities, from 1.2.5
      have s1_2_6 : 5 * (n : ℝ) ≤ 9 * (n : ℝ) - 3 := by parley_order
      -- 1.2.7. inequalities
      have s1_2_7 : 5 * (n : ℝ) > 0 := by parley_order
      -- 1.2.8. transitivity, from 1.2.7, 1.2.6
      have s1_2_8 : 9 * (n : ℝ) - 3 > 0 := by parley_order
      -- 1.2.9. inequalities
      have s1_2_9 : 9 * (n : ℝ) - 3 ≠ 0 := by parley_side
      -- 1.2.10. algebra, from H2
      have r68_1 : 3 * (n : ℝ) - 1 ≠ 0 := by parley_side
      have r68_2 : 9 * (n : ℝ) - 3 ≠ 0 := by parley_side
      have s1_2_10 : a (n : ℤ) - 2 / 3 = 5 * (1 / (9 * (n : ℝ) - 3)) := by linear_combination (norm := parley_field) ((3) / ((3))) * (hH2 n (by parley_side))
      -- 1.2.11. mun:reciprocal-positive x := 9n − 3, from 1.2.8
      have s1_2_11 : 1 / (9 * (n : ℝ) - 3) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := 9 * (n : ℝ) - 3) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := 9 * (n : ℝ) - 3) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := 9 * (n : ℝ) - 3) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := 9 * (n : ℝ) - 3) (by parley_side)); parley_side)
      -- 1.2.12. inequalities
      have r76_1 : 9 * (n : ℝ) - 3 ≠ 0 := by parley_side
      have s1_2_12 : 5 * (1 / (9 * (n : ℝ) - 3)) > 0 := by parley_order
      -- 1.2.13. transitivity, from 1.2.12, 1.2.10
      have r82_1 : 9 * (n : ℝ) - 3 ≠ 0 := by parley_side
      have s1_2_13 : a (n : ℤ) - 2 / 3 > 0 := by parley_order
      -- 1.2.14. inequalities
      have s1_2_14 : a (n : ℤ) > 2 / 3 := by parley_order
      -- 1.2.15. inequalities
      have s1_2_15 : 2 / 3 - ε < 2 / 3 := by parley_order
      -- 1.2.16. transitivity, from 1.2.15, 1.2.14
      have s1_2_16 : 2 / 3 - ε < a (n : ℤ) := by parley_order
      -- 1.2.17. mun:reciprocal-order x := 5n, y := 9n − 3, from 1.2.6
      have r103_1 : 5 * (n : ℝ) > 0 := by parley_side
      have r103_2 : 9 * (n : ℝ) - 3 > 0 := by parley_side
      have s1_2_17 : 1 / (9 * (n : ℝ) - 3) ≤ 1 / (5 * (n : ℝ)) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 5 * (n : ℝ)) (by parley_side) (y := 9 * (n : ℝ) - 3) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 5 * (n : ℝ)) (by parley_side) (y := 9 * (n : ℝ) - 3) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 5 * (n : ℝ)) (by parley_side) (y := 9 * (n : ℝ) - 3) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 5 * (n : ℝ)) (by parley_side) (y := 9 * (n : ℝ) - 3) (by parley_side))).mp (by parley_side); parley_side)
      -- 1.2.18. inequalities
      have r108_1 : 9 * (n : ℝ) - 3 ≠ 0 := by parley_side
      have s1_2_18 : 5 * (1 / (9 * (n : ℝ) - 3)) ≤ 5 * (1 / (5 * (n : ℝ))) := by parley_order
      -- 1.2.19. algebra
      have s1_2_19 : 5 * (1 / (5 * (n : ℝ))) = 1 / (n : ℝ) := by parley_ring
      -- 1.2.20. mun:reciprocal-order x := N, y := n, from A2
      have r117_1 : (N : ℝ) > 0 := by parley_order
      have r117_2 : (n : ℝ) > 0 := by parley_side
      have s1_2_20 : 1 / (n : ℝ) ≤ 1 / (N : ℝ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side); parley_side)
      -- 1.2.21. transitivity, from 1.2.10, 1.2.18, 1.2.19, 1.2.20, 1.1
      have r122_1 : 9 * (n : ℝ) - 3 ≠ 0 := by parley_side
      have s1_2_21 : a (n : ℤ) - 2 / 3 < ε := by parley_order
      -- 1.2.22. inequalities
      have s1_2_22 : a (n : ℤ) < 2 / 3 + ε := by parley_order
      -- 1.2.23. join 1.2.16, 1.2.22
      have s1_2_23 : 2 / 3 - ε < a (n : ℤ) ∧ a (n : ℤ) < 2 / 3 + ε := by parley_side
      -- 1.2.24. mun:abs-difference-lt x := a(n), c := 2/3, δ := ε, from 1.2.23
      have s1_2_24 : abs (a (n : ℤ) - 2 / 3) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := (2 / 3 : ℝ)) (δ := ε))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := (2 / 3 : ℝ)) (δ := ε))).mpr (by parley_side); parley_side)
      all_goals parley_side
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - 2 / 3) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 2. def:tends-to L := 2/3, from 1
  have s2 : Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds (2 / 3)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (2 / 3 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (2 / 3 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.RationalSequenceLimit.RationalSequenceLimit

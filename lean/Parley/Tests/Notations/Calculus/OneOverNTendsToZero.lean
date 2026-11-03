module

public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.OneOverNTendsToZero

theorem one_over_n_tends_to_zero :
    Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ) : ℝ)) Filter.atTop (nhds 0) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (1 / (n : ℝ) - 0) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. obtain N: thm:archimedean x := ε, from A1
    obtain ⟨N, s1_1a, s1_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε) (by parley_side))
    -- 1.2. proof
    have s1_2 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (1 / (n : ℝ) - 0) < ε := by
      intro n hK2
      intro hA2
      -- 1.2.1. mun:reciprocal-order x := N, y := n, from A2
      have r238_1 : (N : ℝ) > 0 := by parley_order
      have r238_2 : (n : ℝ) > 0 := by parley_order
      have s1_2_1 : 1 / (n : ℝ) ≤ 1 / (N : ℝ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side); parley_side)
      -- 1.2.2. mun:reciprocal-positive x := n
      have r243_1 : (n : ℝ) > 0 := by parley_order
      have s1_2_2 : 1 / (n : ℝ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℝ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℝ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℝ)) (by parley_side)); parley_side)
      -- 1.2.3. inequalities
      have s1_2_3 : 0 - ε < 0 := by parley_order
      -- 1.2.4. transitivity, from 1.2.3, 1.2.2
      have s1_2_4 : 0 - ε < 1 / (n : ℝ) := by parley_order
      -- 1.2.5. inequalities, from 1.1
      have s1_2_5 : 1 / (N : ℝ) < ε := by parley_order
      -- 1.2.6. transitivity, from 1.2.1, 1.2.5
      have s1_2_6 : 1 / (n : ℝ) < 0 + ε := by parley_order
      -- 1.2.7. mun:abs-difference-lt x := 1/n, c := 0, δ := ε, from 1.2.4, 1.2.6
      have s1_2_7 : abs (1 / (n : ℝ) - 0) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := 1 / (n : ℝ)) (c := (0 : ℝ)) (δ := ε))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := 1 / (n : ℝ)) (c := (0 : ℝ)) (δ := ε))).mpr (by parley_side); parley_side)
      all_goals parley_side
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (1 / (n : ℝ) - 0) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 2. proof
  -- what this block shows, Lean's types give
  -- 3. def:tends-to L := 0, from 1, 2
  have s3 : Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ) : ℝ)) Filter.atTop (nhds 0) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => 1 / (n : ℝ))) (L := (0 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => 1 / (n : ℝ))) (L := (0 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s3

end Parley.Tests.Notations.Calculus.OneOverNTendsToZero

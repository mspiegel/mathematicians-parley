module

public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/squeeze-for-sequences.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SqueezeForSequences.SqueezeForSequences

set_option maxHeartbeats 600000 in
theorem squeeze_for_sequences (a : ℤ → ℝ) (b : ℤ → ℝ) (c : ℤ → ℝ) (L : ℝ) (hH5 : ∃ M : ℤ, ∀ n : ℕ, 0 < n → (n : ℝ) > (M : ℝ) → a (n : ℤ) ≤ b (n : ℤ) ∧ b (n : ℤ) ≤ c (n : ℤ)) (hH6 : Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds L)) (hH7 : Filter.Tendsto (fun n : ℕ => (c (n : ℤ) : ℝ)) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n : ℕ => (b (n : ℤ) : ℝ)) Filter.atTop (nhds L) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (b (n : ℤ) - L) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. def:tends-to x := a, from H6
    have s1_1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side); parley_side)
    -- 1.2. def:tends-to x := c, from H7
    have s1_2 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (c (n : ℤ) - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := c) (L := L))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := c) (L := L))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := c) (L := L))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := c) (L := L))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := c) (L := L))).mp (by parley_side); parley_side)
    -- 1.3. instantiate ε := ε in line 1.1, from A1
    have s1_3 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - L) < ε) := by first | exact (s1_1 ε (by parley_side)) | exact ((s1_1 ε (by parley_side))).symm | simpa using (s1_1 ε (by parley_side)) | exact_mod_cast (s1_1 ε (by parley_side)) | (have h := (s1_1 ε (by parley_side)); parley_side)
    -- 1.4. instantiate ε := ε in line 1.2, from A1
    have s1_4 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (c (n : ℤ) - L) < ε) := by first | exact (s1_2 ε (by parley_side)) | exact ((s1_2 ε (by parley_side))).symm | simpa using (s1_2 ε (by parley_side)) | exact_mod_cast (s1_2 ε (by parley_side)) | (have h := (s1_2 ε (by parley_side)); parley_side)
    -- 1.5. obtain P from line 1.3
    obtain ⟨P, s1_5a, s1_5b⟩ := s1_3
    try lift P to ℕ using le_of_lt s1_5a
    -- 1.6. obtain Q from line 1.4
    obtain ⟨Q, s1_6a, s1_6b⟩ := s1_4
    try lift Q to ℕ using le_of_lt s1_6a
    -- 1.7. obtain M from H5
    obtain ⟨M, s1_7⟩ := hH5
    -- 1.8. obtain R: thm:archimedean-natural x := M
    obtain ⟨R, s1_8a, s1_8b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean_natural (x := (M : ℝ)))
    try lift R to ℕ using le_of_lt s1_8a
    -- 1.9. inequalities, from 1.6, 1.8
    have s1_9 : (Q : ℝ) + (R : ℝ) > 0 := by have := (s1_6b R (by parley_side)); parley_order
    -- 1.10. inequalities
    have s1_10 : (P : ℝ) + (Q : ℝ) + (R : ℝ) ≥ (P : ℝ) := by parley_order
    -- 1.11. inequalities, from 1.5, 1.8
    have s1_11 : (P : ℝ) + (R : ℝ) > 0 := by have := (s1_5b R (by parley_side)); parley_order
    -- 1.12. inequalities
    have s1_12 : (P : ℝ) + (Q : ℝ) + (R : ℝ) ≥ (Q : ℝ) := by parley_order
    -- 1.13. inequalities, from 1.5, 1.6
    have s1_13 : (P : ℝ) + (Q : ℝ) > 0 := by have := (s1_5b Q (by parley_side)); have := (s1_6b P (by parley_side)); parley_order
    -- 1.14. inequalities
    have s1_14 : (P : ℝ) + (Q : ℝ) + (R : ℝ) > (R : ℝ) := by parley_order
    -- 1.15. proof
    have s1_15 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (P : ℝ) + (Q : ℝ) + (R : ℝ) → abs (b (n : ℤ) - L) < ε := by
      intro n hK2
      intro hA2
      -- 1.15.1. transitivity, from A2, 1.10
      have s1_15_1 : (n : ℝ) ≥ (P : ℝ) := by parley_order
      -- 1.15.2. transitivity, from A2, 1.12
      have s1_15_2 : (n : ℝ) ≥ (Q : ℝ) := by parley_order
      -- 1.15.3. transitivity, from A2, 1.14, 1.8
      have s1_15_3 : (n : ℝ) > (M : ℝ) := by parley_order
      -- 1.15.4. instantiate n := n in line 1.5, from 1.15.1
      have s1_15_4 : abs (a (n : ℤ) - L) < ε := by first | linarith [(s1_5b n (by parley_side) (by parley_side))] | (have h := (s1_5b n (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1_5b n (by parley_side) (by parley_side)) | (have h := (s1_5b n (by parley_side) (by parley_side)); parley_side)
      -- 1.15.5. instantiate n := n in line 1.6, from 1.15.2
      have s1_15_5 : abs (c (n : ℤ) - L) < ε := by first | linarith [(s1_6b n (by parley_side) (by parley_side))] | (have h := (s1_6b n (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1_6b n (by parley_side) (by parley_side)) | (have h := (s1_6b n (by parley_side) (by parley_side)); parley_side)
      -- 1.15.6. instantiate n := n in line 1.7, from 1.15.3
      have s1_15_6 : a (n : ℤ) ≤ b (n : ℤ) ∧ b (n : ℤ) ≤ c (n : ℤ) := by first | exact (s1_7 n (by parley_side) (by parley_side)) | exact ((s1_7 n (by parley_side) (by parley_side))).symm | simpa using (s1_7 n (by parley_side) (by parley_side)) | exact_mod_cast (s1_7 n (by parley_side) (by parley_side)) | (have h := (s1_7 n (by parley_side) (by parley_side)); parley_side)
      -- 1.15.7. mun:abs-difference-lt x := a(n), c := L, δ := ε, from 1.15.4
      have s1_15_7 : L - ε < a (n : ℤ) := by first | linarith [(((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := L) (δ := ε))).mp (by parley_side)).1] | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := L) (δ := ε))).mp (by parley_side)).1; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := L) (δ := ε))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := L) (δ := ε))).mp (by parley_side)).1; parley_side)
      -- 1.15.8. mun:abs-difference-lt x := c(n), c := L, δ := ε, from 1.15.5
      have s1_15_8 : c (n : ℤ) < L + ε := by first | linarith [(((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := c (n : ℤ)) (c := L) (δ := ε))).mp (by parley_side)).2] | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := c (n : ℤ)) (c := L) (δ := ε))).mp (by parley_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := c (n : ℤ)) (c := L) (δ := ε))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := c (n : ℤ)) (c := L) (δ := ε))).mp (by parley_side)).2; parley_side)
      -- 1.15.9. transitivity, from 1.15.7, 1.15.6
      have s1_15_9 : L - ε < b (n : ℤ) := by parley_order
      -- 1.15.10. transitivity, from 1.15.6, 1.15.8
      have s1_15_10 : b (n : ℤ) < L + ε := by parley_order
      -- 1.15.11. join 1.15.9, 1.15.10
      have s1_15_11 : L - ε < b (n : ℤ) ∧ b (n : ℤ) < L + ε := by parley_side
      -- 1.15.12. mun:abs-difference-lt x := b(n), c := L, δ := ε, from 1.15.11
      have s1_15_12 : abs (b (n : ℤ) - L) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := b (n : ℤ)) (c := L) (δ := ε))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := b (n : ℤ)) (c := L) (δ := ε))).mpr (by parley_side); parley_side)
      all_goals parley_side
    -- 1.16. exhibit, from 1.15
    have s1_16 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (b (n : ℤ) - L) < ε) := ⟨P + Q + R, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 2. def:tends-to x := b, from 1
  have s2 : Filter.Tendsto (fun n : ℕ => (b (n : ℤ) : ℝ)) Filter.atTop (nhds L) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := b) (L := L))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := b) (L := L))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SqueezeForSequences.SqueezeForSequences

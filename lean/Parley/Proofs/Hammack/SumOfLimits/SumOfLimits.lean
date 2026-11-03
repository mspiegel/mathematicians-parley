module

public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/sum-of-limits.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfLimits.SumOfLimits

theorem sum_of_limits (a : ℤ → ℝ) (b : ℤ → ℝ) (L : ℝ) (M : ℝ) (hH5 : Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds L)) (hH6 : Filter.Tendsto (fun n : ℕ => (b (n : ℤ) : ℝ)) Filter.atTop (nhds M)) :
    Filter.Tendsto (fun n : ℕ => (a (n : ℤ) + b (n : ℤ) : ℝ)) Filter.atTop (nhds (L + M)) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) + b (n : ℤ) - (L + M)) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. inequalities
    have s1_1 : ε / 2 > 0 := by parley_order
    -- 1.2. def:tends-to, from H5
    have s1_2 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side); parley_side)
    -- 1.3. def:tends-to x := b, L := M, from H6
    have s1_3 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (b (n : ℤ) - M) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := b) (L := M))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := b) (L := M))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := b) (L := M))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := b) (L := M))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := b) (L := M))).mp (by parley_side); parley_side)
    -- 1.4. instantiate ε := ε/2 in line 1.2, from 1.1
    have s1_4 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - L) < ε / 2) := by first | exact (s1_2 (ε / 2) (by parley_side)) | exact ((s1_2 (ε / 2) (by parley_side))).symm | simpa using (s1_2 (ε / 2) (by parley_side)) | exact_mod_cast (s1_2 (ε / 2) (by parley_side)) | (have h := (s1_2 (ε / 2) (by parley_side)); parley_side)
    -- 1.5. instantiate ε := ε/2 in line 1.3, from 1.1
    have s1_5 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (b (n : ℤ) - M) < ε / 2) := by first | exact (s1_3 (ε / 2) (by parley_side)) | exact ((s1_3 (ε / 2) (by parley_side))).symm | simpa using (s1_3 (ε / 2) (by parley_side)) | exact_mod_cast (s1_3 (ε / 2) (by parley_side)) | (have h := (s1_3 (ε / 2) (by parley_side)); parley_side)
    -- 1.6. obtain P from line 1.4
    obtain ⟨P, s1_6a, s1_6b⟩ := s1_4
    -- 1.7. obtain Q from line 1.5
    obtain ⟨Q, s1_7a, s1_7b⟩ := s1_5
    -- 1.8. inequalities, from 1.7
    have s1_8 : (Q : ℝ) > 0 := by parley_order
    -- 1.9. inequalities
    have s1_9 : (P : ℝ) + (Q : ℝ) ≥ (P : ℝ) := by parley_order
    -- 1.10. inequalities, from 1.6
    have s1_10 : (P : ℝ) > 0 := by parley_order
    -- 1.11. inequalities
    have s1_11 : (P : ℝ) + (Q : ℝ) ≥ (Q : ℝ) := by parley_order
    -- 1.12. proof
    have s1_12 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (P : ℝ) + (Q : ℝ) → abs (a (n : ℤ) + b (n : ℤ) - (L + M)) < ε := by
      intro n hK2
      intro hA2
      -- 1.12.1. transitivity, from A2, 1.9
      have s1_12_1 : (n : ℝ) ≥ (P : ℝ) := by parley_order
      -- 1.12.2. transitivity, from A2, 1.11
      have s1_12_2 : (n : ℝ) ≥ (Q : ℝ) := by parley_order
      -- 1.12.3. instantiate n := n in line 1.6, from 1.12.1
      have s1_12_3 : abs (a (n : ℤ) - L) < ε / 2 := by first | linarith [(s1_6b n (by parley_side) (by parley_side))] | (have h := (s1_6b n (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1_6b n (by parley_side) (by parley_side)) | (have h := (s1_6b n (by parley_side) (by parley_side)); parley_side)
      -- 1.12.4. instantiate n := n in line 1.7, from 1.12.2
      have s1_12_4 : abs (b (n : ℤ) - M) < ε / 2 := by first | linarith [(s1_7b n (by parley_side) (by parley_side))] | (have h := (s1_7b n (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1_7b n (by parley_side) (by parley_side)) | (have h := (s1_7b n (by parley_side) (by parley_side)); parley_side)
      -- 1.12.5. mun:abs-difference-lt x := a(n), c := L, δ := ε/2, from 1.12.3
      have s1_12_5 : L - ε / 2 < a (n : ℤ) ∧ a (n : ℤ) < L + ε / 2 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := L) (δ := ε / 2))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := L) (δ := ε / 2))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := L) (δ := ε / 2))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := L) (δ := ε / 2))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := L) (δ := ε / 2))).mp (by parley_side); parley_side)
      -- 1.12.6. mun:abs-difference-lt x := b(n), c := M, δ := ε/2, from 1.12.4
      have s1_12_6 : M - ε / 2 < b (n : ℤ) ∧ b (n : ℤ) < M + ε / 2 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := b (n : ℤ)) (c := M) (δ := ε / 2))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := b (n : ℤ)) (c := M) (δ := ε / 2))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := b (n : ℤ)) (c := M) (δ := ε / 2))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := b (n : ℤ)) (c := M) (δ := ε / 2))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := b (n : ℤ)) (c := M) (δ := ε / 2))).mp (by parley_side); parley_side)
      -- 1.12.7. inequalities, from 1.12.5, 1.12.6
      have s1_12_7 : L + M - ε < a (n : ℤ) + b (n : ℤ) := by parley_order
      -- 1.12.8. inequalities, from 1.12.5, 1.12.6
      have s1_12_8 : a (n : ℤ) + b (n : ℤ) < L + M + ε := by parley_order
      -- 1.12.9. join 1.12.7, 1.12.8
      have s1_12_9 : L + M - ε < a (n : ℤ) + b (n : ℤ) ∧ a (n : ℤ) + b (n : ℤ) < L + M + ε := by parley_side
      -- 1.12.10. mun:abs-difference-lt x := a(n) + b(n), c := L + M, δ := ε, from 1.12.9
      have s1_12_10 : abs (a (n : ℤ) + b (n : ℤ) - (L + M)) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ) + b (n : ℤ)) (c := L + M) (δ := ε))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ) + b (n : ℤ)) (c := L + M) (δ := ε))).mpr (by parley_side); parley_side)
      all_goals parley_side
    -- 1.13. exhibit, from 1.12
    have s1_13 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) + b (n : ℤ) - (L + M)) < ε) := ⟨P + Q, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 2. def:tends-to L := L + M, from 1
  have s2 : Filter.Tendsto (fun n : ℕ => (a (n : ℤ) + b (n : ℤ) : ℝ)) Filter.atTop (nhds (L + M)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => a n + b n)) (L := L + M))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => a n + b n)) (L := L + M))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SumOfLimits.SumOfLimits

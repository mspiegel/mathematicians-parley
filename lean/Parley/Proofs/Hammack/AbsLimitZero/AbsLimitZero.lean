module

public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/abs-limit-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AbsLimitZero.AbsLimitZero

set_option maxHeartbeats 400000 in
theorem abs_limit_zero (a : ℤ → ℝ) (hH2 : Filter.Tendsto (fun n : ℕ => (abs (a (n : ℤ)) : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds 0) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ)) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. def:tends-to L := 0, from H2
    have s1_1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (abs (a (n : ℤ)) - 0) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => abs (a n))) (L := (0 : ℝ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => abs (a n))) (L := (0 : ℝ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => abs (a n))) (L := (0 : ℝ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => abs (a n))) (L := (0 : ℝ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => abs (a n))) (L := (0 : ℝ)))).mp (by parley_side); parley_side)
    -- 1.2. instantiate ε := ε in line 1.1, from A1
    have s1_2 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (abs (a (n : ℤ))) < ε) := by first | exact (s1_1 ε (by parley_side)) | exact ((s1_1 ε (by parley_side))).symm | simpa using (s1_1 ε (by parley_side)) | exact_mod_cast (s1_1 ε (by parley_side)) | (have h := (s1_1 ε (by parley_side)); parley_side)
    -- 1.3. obtain N from line 1.2
    obtain ⟨N, s1_3a, s1_3b⟩ := s1_2
    try lift N to ℕ using le_of_lt s1_3a
    -- 1.4. proof
    have s1_4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ)) < ε := by
      intro n hK2
      intro hA2
      -- 1.4.1. instantiate n := n in line 1.3, from A2
      have s1_4_1 : abs (abs (a (n : ℤ))) < ε := by first | linarith [(s1_3b n (by parley_side) (by parley_side))] | (have h := (s1_3b n (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1_3b n (by parley_side) (by parley_side)) | (have h := (s1_3b n (by parley_side) (by parley_side)); parley_side)
      -- 1.4.2. membership, from H1
      -- 1.4.3. mun:abs-nonneg x := a(n), from 1.4.2
      have s1_4_3 : abs (a (n : ℤ)) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (a (n : ℤ) : ℂ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (a (n : ℤ) : ℂ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (a (n : ℤ) : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (a (n : ℤ) : ℂ))); parley_side)
      -- 1.4.4. mun:abs-real x := a(n), from 1.4.2
      -- 1.4.5. def:abs x := |a(n)|, from 1.4.3, 1.4.4
      have s1_4_5 : abs (abs (a (n : ℤ))) = abs (a (n : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs (a (n : ℤ)))) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs (a (n : ℤ)))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs (a (n : ℤ)))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs (a (n : ℤ)))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs (a (n : ℤ)))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs (a (n : ℤ)))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs (a (n : ℤ)))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs (a (n : ℤ)))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs (a (n : ℤ)))) (by parley_side); parley_side)
      -- 1.4.6. substitute ||a(n)|| = |a(n)| (line 1.4.5) into line 1.4.1
      have s1_4_6 : abs (a (n : ℤ)) < ε := by parley_subst_at s1_4_5 s1_4_1
      all_goals parley_side
    -- 1.5. exhibit, from 1.4
    have s1_5 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ)) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 2. def:tends-to L := 0, from 1
  have s2 : Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds 0) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (0 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (0 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.AbsLimitZero.AbsLimitZero

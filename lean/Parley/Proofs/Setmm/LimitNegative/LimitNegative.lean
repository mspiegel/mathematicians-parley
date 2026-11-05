module

public import AlgebraTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/limit-negative.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitNegative.LimitNegative

theorem limit_negative (x : ℤ → ℝ) (L : ℝ) (hH3 : Filter.Tendsto (fun n : ℕ => (x (n : ℤ) : ℝ)) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n : ℕ => (-x (n : ℤ) : ℝ)) Filter.atTop (nhds (-L)) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (-x (n : ℤ) - -L) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. def:tends-to, from H3
    have s1_1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (x (n : ℤ) - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side); parley_side)
    -- 1.2. instantiate ε := ε in line 1.1, from A1
    have s1_2 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (x (n : ℤ) - L) < ε) := by first | exact (s1_1 ε (by parley_side)) | exact ((s1_1 ε (by parley_side))).symm | simpa using (s1_1 ε (by parley_side)) | exact_mod_cast (s1_1 ε (by parley_side)) | (have h := (s1_1 ε (by parley_side)); parley_side)
    -- 1.3. obtain N from line 1.2
    obtain ⟨N, s1_3a, s1_3b⟩ := s1_2
    try lift N to ℕ using le_of_lt s1_3a
    -- 1.4. proof
    have s1_4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (-x (n : ℤ) - -L) < ε := by
      intro n hK2
      intro hA2
      -- 1.4.1. instantiate n := n in line 1.3, from A2
      have s1_4_1 : abs (x (n : ℤ) - L) < ε := by first | linarith [(s1_3b n (by parley_side) (by parley_side))] | (have h := (s1_3b n (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1_3b n (by parley_side) (by parley_side)) | (have h := (s1_3b n (by parley_side) (by parley_side)); parley_side)
      -- 1.4.2. membership, from H1
      -- 1.4.3. algebra
      have s1_4_3 : -x (n : ℤ) - -L = -(x (n : ℤ) - L) := by parley_ring
      -- 1.4.4. calculation
      have s1_4_4 : abs (-x (n : ℤ) - -L) = abs (x (n : ℤ) - L) := by
        calc abs (-x (n : ℤ) - -L) = abs (-(x (n : ℤ) - L)) := by parley_subst s1_4_3
          _ = abs (x (n : ℤ) - L) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x (n : ℤ) - L)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x (n : ℤ) - L)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x (n : ℤ) - L)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x (n : ℤ) - L)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x (n : ℤ) - L))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x (n : ℤ) - L)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x (n : ℤ) - L)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x (n : ℤ) - L)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x (n : ℤ) - L)); parley_side)
      -- 1.4.5. substitute |−x(n) − −L| = |x(n) − L| (line 1.4.4) into line 1.4.1
      have s1_4_5 : abs (-x (n : ℤ) - -L) < ε := by parley_subst_at s1_4_4 s1_4_1
      all_goals parley_side
    -- 1.5. exhibit, from 1.4
    have s1_5 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (-x (n : ℤ) - -L) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 2. def:tends-to L := −L, from 1
  have s2 : Filter.Tendsto (fun n : ℕ => (-x (n : ℤ) : ℝ)) Filter.atTop (nhds (-L)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => -x n)) (L := -L))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => -x n)) (L := -L))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Setmm.LimitNegative.LimitNegative

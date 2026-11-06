module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from proofs/setmm/limit-add-constant.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitAddConstant.LimitAddConstant

theorem limit_add_constant (x : ℤ → ℝ) (L : ℝ) (C : ℝ) (hH4 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n : ℤ => (x n + C : ℝ)) Filter.atTop (nhds (L + C)) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n + C - (L + C)) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. def:tends-to, from H4
    have s1_1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side); parley_side)
    -- 1.2. instantiate ε := ε in line 1.1, from A1
    have s1_2 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < ε) := by first | exact (s1_1 ε (by parley_side)) | exact ((s1_1 ε (by parley_side))).symm | simpa using (s1_1 ε (by parley_side)) | exact_mod_cast (s1_1 ε (by parley_side)) | (have h := (s1_1 ε (by parley_side)); parley_side)
    -- 1.3. obtain N from line 1.2
    obtain ⟨N, s1_3a, s1_3b⟩ := s1_2
    -- 1.4. proof
    have s1_4 : ∀ n : ℤ, 0 < n → n ≥ N → abs (x n + C - (L + C)) < ε := by
      intro n hK2
      intro hA2
      -- 1.4.1. instantiate n := n in line 1.3, from A2
      have s1_4_1 : abs (x n - L) < ε := by first | linarith [(s1_3b n (by parley_side) (by parley_side))] | (have h := (s1_3b n (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1_3b n (by parley_side) (by parley_side)) | (have h := (s1_3b n (by parley_side) (by parley_side)); parley_side)
      -- 1.4.2. substitute
      have s1_4_2 : abs (x n + C - (L + C)) < ε := by
        have c1 : x n - L = x n + C - (L + C) := by parley_ring
        have row1 : abs (x n + C - (L + C)) < ε := by parley_subst_at c1 s1_4_1
        exact row1
      all_goals parley_side
    -- 1.5. exhibit, from 1.4
    have s1_5 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n + C - (L + C)) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 2. def:tends-to L := L + C, from 1
  have s2 : Filter.Tendsto (fun n : ℤ => (x n + C : ℝ)) Filter.atTop (nhds (L + C)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => x n + C)) (L := L + C))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => x n + C)) (L := L + C))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Setmm.LimitAddConstant.LimitAddConstant

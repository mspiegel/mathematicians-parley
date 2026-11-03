module

public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/divergent-has-no-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DivergentHasNoLimit.DivergentHasNoLimit

theorem divergent_has_no_limit (a : ℤ → ℝ) (hH2 : ∀ M : ℝ, ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) > (N : ℝ) → a (n : ℤ) > M)) :
    ¬ (∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds L)) := by
  -- the theorem. contradiction
  have sThm : ¬ (∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds L)) := by
    by_contra hc_hS
    have hS : ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds L) := by parley_suppose hc_hS
    -- 1. obtain L from S
    obtain ⟨L, s1⟩ := hS
    -- 2. def:tends-to, from 1
    have s2 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side); parley_side)
    -- 3. instantiate ε := 1 in line 2
    have r22_1 : (0 : ℝ) < 1 := by parley_arith
    have s3 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - L) < 1) := by first | exact (s2 (1 : ℝ) (by parley_side)) | exact ((s2 (1 : ℝ) (by parley_side))).symm | simpa using (s2 (1 : ℝ) (by parley_side)) | exact_mod_cast (s2 (1 : ℝ) (by parley_side)) | (have h := (s2 (1 : ℝ) (by parley_side)); parley_side)
    -- 4. obtain P from line 3
    obtain ⟨P, s4a, s4b⟩ := s3
    -- 5. instantiate M := L + 1 in H2
    have s5 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) > (N : ℝ) → a (n : ℤ) > L + 1) := by first | exact (hH2 (L + 1)) | exact ((hH2 (L + 1))).symm | simpa using (hH2 (L + 1)) | exact_mod_cast (hH2 (L + 1)) | (have h := (hH2 (L + 1)); parley_side)
    -- 6. obtain Q from line 5
    obtain ⟨Q, s6a, s6b⟩ := s5
    -- 7. inequalities, from 6
    have s7 : (Q : ℝ) > 0 := by parley_order
    -- 8. inequalities
    have s8 : (P : ℝ) + (Q : ℝ) ≥ (P : ℝ) := by parley_order
    -- 9. inequalities, from 4
    have s9 : (P : ℝ) > 0 := by parley_order
    -- 10. inequalities
    have s10 : (P : ℝ) + (Q : ℝ) > (Q : ℝ) := by parley_order
    -- 11. instantiate n := P + Q in line 4, from 8
    have s11 : abs (a ((P : ℤ) + (Q : ℤ)) - L) < 1 := by first | linarith [(s4b (P + Q) (by parley_side) (by parley_side))] | (have h := (s4b (P + Q) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s4b (P + Q) (by parley_side) (by parley_side)) | (have h := (s4b (P + Q) (by parley_side) (by parley_side)); parley_side)
    -- 12. instantiate n := P + Q in line 6, from 10
    have s12 : a ((P : ℤ) + (Q : ℤ)) > L + 1 := by first | linarith [(s6b (P + Q) (by parley_side) (by parley_side))] | (have h := (s6b (P + Q) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s6b (P + Q) (by parley_side) (by parley_side)) | (have h := (s6b (P + Q) (by parley_side) (by parley_side)); parley_side)
    -- 13. mun:abs-difference-lt x := a(P + Q), c := L, δ := 1, from 11
    have s13 : L - 1 < a ((P : ℤ) + (Q : ℤ)) ∧ a ((P : ℤ) + (Q : ℤ)) < L + 1 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a ((P : ℤ) + (Q : ℤ))) (c := L) (δ := (1 : ℝ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a ((P : ℤ) + (Q : ℤ))) (c := L) (δ := (1 : ℝ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a ((P : ℤ) + (Q : ℤ))) (c := L) (δ := (1 : ℝ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a ((P : ℤ) + (Q : ℤ))) (c := L) (δ := (1 : ℝ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a ((P : ℤ) + (Q : ℤ))) (c := L) (δ := (1 : ℝ)))).mp (by parley_side); parley_side)
    -- 14. inequalities
    have s14 : a ((P : ℤ) + (Q : ℤ)) ≤ L + 1 := by parley_order
    -- 15. inequalities, from 14
    have s15 : ¬ a ((P : ℤ) + (Q : ℤ)) > L + 1 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.DivergentHasNoLimit.DivergentHasNoLimit

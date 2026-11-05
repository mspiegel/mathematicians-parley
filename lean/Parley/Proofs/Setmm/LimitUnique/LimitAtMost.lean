module

public import ArithTactics
public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/limit-unique.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitUnique.LimitAtMost

set_option maxHeartbeats 400000 in
theorem limit_at_most (x : ℤ → ℝ) (A : ℝ) (B : ℝ) (hH4 : Filter.Tendsto (fun n : ℕ => (x (n : ℤ) : ℝ)) Filter.atTop (nhds A)) (hH5 : Filter.Tendsto (fun n : ℕ => (x (n : ℤ) : ℝ)) Filter.atTop (nhds B)) :
    A ≤ B := by
  -- 1. proof
  have s1 : ∀ r : ℝ, r > 0 → A < B + r := by
    intro r
    intro hA1
    -- 1.1. inequalities
    have s1_1 : r / 2 > 0 := by parley_order
    -- 1.2. def:tends-to, from H4
    have s1_2 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (x (n : ℤ) - A) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := A))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := A))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := A))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := A))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := A))).mp (by parley_side); parley_side)
    -- 1.3. def:tends-to L := B, from H5
    have s1_3 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (x (n : ℤ) - B) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := B))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := B))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := B))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := B))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := B))).mp (by parley_side); parley_side)
    -- 1.4. instantiate ε := r/2 in line 1.2, from 1.1
    have s1_4 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (x (n : ℤ) - A) < r / 2) := by first | exact (s1_2 (r / 2) (by parley_side)) | exact ((s1_2 (r / 2) (by parley_side))).symm | simpa using (s1_2 (r / 2) (by parley_side)) | exact_mod_cast (s1_2 (r / 2) (by parley_side)) | (have h := (s1_2 (r / 2) (by parley_side)); parley_side)
    -- 1.5. instantiate ε := r/2 in line 1.3, from 1.1
    have s1_5 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (x (n : ℤ) - B) < r / 2) := by first | exact (s1_3 (r / 2) (by parley_side)) | exact ((s1_3 (r / 2) (by parley_side))).symm | simpa using (s1_3 (r / 2) (by parley_side)) | exact_mod_cast (s1_3 (r / 2) (by parley_side)) | (have h := (s1_3 (r / 2) (by parley_side)); parley_side)
    -- 1.6. obtain P from line 1.4
    obtain ⟨P, s1_6a, s1_6b⟩ := s1_4
    try lift P to ℕ using le_of_lt s1_6a
    -- 1.7. obtain Q from line 1.5
    obtain ⟨Q, s1_7a, s1_7b⟩ := s1_5
    try lift Q to ℕ using le_of_lt s1_7a
    -- 1.8. inequalities, from 1.7
    have s1_8 : (P : ℝ) + (Q : ℝ) ≥ (P : ℝ) := by have := (s1_7b P (by parley_side)); parley_order
    -- 1.9. inequalities, from 1.6
    have s1_9 : (P : ℝ) + (Q : ℝ) ≥ (Q : ℝ) := by have := (s1_6b Q (by parley_side)); parley_order
    -- 1.10. instantiate n := P + Q in line 1.6, from 1.8
    have s1_10 : abs (x ((P : ℤ) + (Q : ℤ)) - A) < r / 2 := by first | linarith [(s1_6b (P + Q) (by parley_side) (by parley_side))] | (have h := (s1_6b (P + Q) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1_6b (P + Q) (by parley_side) (by parley_side)) | (have h := (s1_6b (P + Q) (by parley_side) (by parley_side)); parley_side)
    -- 1.11. instantiate n := P + Q in line 1.7, from 1.9
    have s1_11 : abs (x ((P : ℤ) + (Q : ℤ)) - B) < r / 2 := by first | linarith [(s1_7b (P + Q) (by parley_side) (by parley_side))] | (have h := (s1_7b (P + Q) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1_7b (P + Q) (by parley_side) (by parley_side)) | (have h := (s1_7b (P + Q) (by parley_side) (by parley_side)); parley_side)
    -- 1.12. membership, from H1
    -- 1.13. mun:abs-difference-lt x := x(P + Q), c := A, δ := r/2, from 1.10, 1.12
    have s1_13 : A - r / 2 < x ((P : ℤ) + (Q : ℤ)) ∧ x ((P : ℤ) + (Q : ℤ)) < A + r / 2 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((P : ℤ) + (Q : ℤ))) (c := A) (δ := r / 2))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((P : ℤ) + (Q : ℤ))) (c := A) (δ := r / 2))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((P : ℤ) + (Q : ℤ))) (c := A) (δ := r / 2))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((P : ℤ) + (Q : ℤ))) (c := A) (δ := r / 2))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((P : ℤ) + (Q : ℤ))) (c := A) (δ := r / 2))).mp (by parley_side); parley_side)
    -- 1.14. mun:abs-difference-lt x := x(P + Q), c := B, δ := r/2, from 1.11, 1.12
    have s1_14 : B - r / 2 < x ((P : ℤ) + (Q : ℤ)) ∧ x ((P : ℤ) + (Q : ℤ)) < B + r / 2 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((P : ℤ) + (Q : ℤ))) (c := B) (δ := r / 2))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((P : ℤ) + (Q : ℤ))) (c := B) (δ := r / 2))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((P : ℤ) + (Q : ℤ))) (c := B) (δ := r / 2))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((P : ℤ) + (Q : ℤ))) (c := B) (δ := r / 2))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((P : ℤ) + (Q : ℤ))) (c := B) (δ := r / 2))).mp (by parley_side); parley_side)
    -- 1.15. inequalities, from 1.12, 1.13
    have s1_15 : A - r / 2 < x ((P : ℤ) + (Q : ℤ)) := by parley_order
    -- 1.16. inequalities, from 1.12, 1.14
    have s1_16 : x ((P : ℤ) + (Q : ℤ)) < B + r / 2 := by parley_order
    -- 1.17. transitivity, from 1.15, 1.16
    have s1_17 : A - r / 2 < B + r / 2 := by parley_order
    -- 1.18. inequalities
    have s1_18 : A < B + r := by parley_order
    all_goals parley_side
  -- 2. contradiction
  have s2 : A ≤ B := by
    by_contra hc_hS
    have hS : ¬ A ≤ B := by parley_suppose hc_hS
    -- 2.1. inequalities, from S
    have s2_1 : B < A := by parley_order
    -- 2.2. inequalities
    have s2_2 : (A - B) / 2 > 0 := by parley_order
    -- 2.3. instantiate r := (A − B)/2 in line 1, from 2.2
    have s2_3 : A < B + (A - B) / 2 := by first | linarith [(s1 ((A - B) / 2) (by parley_side))] | (have h := (s1 ((A - B) / 2) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 ((A - B) / 2) (by parley_side)) | (have h := (s1 ((A - B) / 2) (by parley_side)); parley_side)
    -- 2.4. inequalities
    have s2_4 : A ≤ B := by parley_order
    all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.LimitUnique.LimitAtMost

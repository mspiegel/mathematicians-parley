module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.LimitAtLeast

theorem limit_at_least (x : ℤ → ℝ) (L : ℝ) (hH3 : Filter.Tendsto (fun n : ℕ => (x (n : ℤ) : ℝ)) Filter.atTop (nhds L)) (B : ℝ) (N : ℕ) (hH5 : 0 < N) (hH6 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → B ≤ x (n : ℤ)) :
    B ≤ L := by
  -- the theorem. contradiction
  have sThm : B ≤ L := by
    by_contra hc_hS
    have hS : ¬ B ≤ L := by parley_suppose hc_hS
    -- 1. inequalities, from S
    have s1 : L < B := by parley_order
    -- 2. inequalities
    have s2 : B - L > 0 := by parley_order
    -- 3. def:tends-to, from H3
    have s3 : ∀ ε : ℝ, ε > 0 → (∃ M : ℕ, 0 < M ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (M : ℝ) → abs (x (n : ℤ) - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side); parley_side)
    -- 4. instantiate ε := B − L in line 3, from 2
    have s4 : ∃ M : ℕ, 0 < M ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (M : ℝ) → abs (x (n : ℤ) - L) < B - L) := by first | exact (s3 (B - L) (by parley_side)) | exact ((s3 (B - L) (by parley_side))).symm | simpa using (s3 (B - L) (by parley_side)) | exact_mod_cast (s3 (B - L) (by parley_side)) | (have h := (s3 (B - L) (by parley_side)); parley_side)
    -- 5. obtain M from line 4
    obtain ⟨M, s5a, s5b⟩ := s4
    -- 6. inequalities, from H5
    have s6 : (M : ℝ) + (N : ℝ) ≥ (M : ℝ) := by parley_order
    -- 7. inequalities, from 5
    have s7 : (M : ℝ) + (N : ℝ) ≥ (N : ℝ) := by have := (s5b N (by parley_side)); parley_order
    -- 8. instantiate n := M + N in line 5, from 6
    have s8 : abs (x ((M : ℤ) + (N : ℤ)) - L) < B - L := by first | linarith [(s5b (M + N) (by parley_side) (by parley_side))] | (have h := (s5b (M + N) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s5b (M + N) (by parley_side) (by parley_side)) | (have h := (s5b (M + N) (by parley_side) (by parley_side)); parley_side)
    -- 9. instantiate n := M + N in H6, from 7
    have s9 : B ≤ x ((M : ℤ) + (N : ℤ)) := by first | linarith [(hH6 (M + N) (by parley_side) (by parley_side))] | (have h := (hH6 (M + N) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (hH6 (M + N) (by parley_side) (by parley_side)) | (have h := (hH6 (M + N) (by parley_side) (by parley_side)); parley_side)
    -- 10. membership, from H1
    -- 11. mun:abs-difference-lt x := x(M + N), c := L, δ := B − L, from 8, 10
    have s11 : L - (B - L) < x ((M : ℤ) + (N : ℤ)) ∧ x ((M : ℤ) + (N : ℤ)) < L + (B - L) := by first | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((M : ℤ) + (N : ℤ))) (c := L) (δ := B - L))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((M : ℤ) + (N : ℤ))) (c := L) (δ := B - L))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((M : ℤ) + (N : ℤ))) (c := L) (δ := B - L))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((M : ℤ) + (N : ℤ))) (c := L) (δ := B - L))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x ((M : ℤ) + (N : ℤ))) (c := L) (δ := B - L))).mp (by parley_side); parley_side)
    -- 12. inequalities, from 10, 11
    have s12 : x ((M : ℤ) + (N : ℤ)) < L + (B - L) := by parley_order
    -- 13. substitute
    have s13 : x ((M : ℤ) + (N : ℤ)) < B := by
      have c1 : L + (B - L) = B := by parley_ring
      have row1 : x ((M : ℤ) + (N : ℤ)) < B := by parley_subst_at c1 s12
      exact row1
    -- 14. inequalities, from 10, 13
    have s14 : ¬ B ≤ x ((M : ℤ) + (N : ℤ)) := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Stdlib.Calculus.LimitAtLeast

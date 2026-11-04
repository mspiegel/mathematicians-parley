module

public import ArithTactics
public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.OneOverNDoesNotTendToOne

theorem one_over_n_does_not_tend_to_one :
    ¬ Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ) : ℝ)) Filter.atTop (nhds 1) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. contradiction
  have s2 : ¬ Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ) : ℝ)) Filter.atTop (nhds 1) := by
    by_contra hc_hS
    have hS : Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ) : ℝ)) Filter.atTop (nhds 1) := by parley_suppose hc_hS
    -- 2.1. def:tends-to L := 1, from S, 1
    have s2_1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (1 / (n : ℝ) - 1) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => 1 / (n : ℝ))) (L := (1 : ℝ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => 1 / (n : ℝ))) (L := (1 : ℝ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => 1 / (n : ℝ))) (L := (1 : ℝ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => 1 / (n : ℝ))) (L := (1 : ℝ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => 1 / (n : ℝ))) (L := (1 : ℝ)))).mp (by parley_side); parley_side)
    -- 2.2. instantiate ε := 1/2 in line 2.1
    have r296_1 : (0 : ℝ) < 1 / 2 := by parley_arith
    have s2_2 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (1 / (n : ℝ) - 1) < 1 / 2) := by first | exact (s2_1 (1 / 2 : ℝ) (by parley_side)) | exact ((s2_1 (1 / 2 : ℝ) (by parley_side))).symm | simpa using (s2_1 (1 / 2 : ℝ) (by parley_side)) | exact_mod_cast (s2_1 (1 / 2 : ℝ) (by parley_side)) | (have h := (s2_1 (1 / 2 : ℝ) (by parley_side)); parley_side)
    -- 2.3. obtain N from line 2.2
    obtain ⟨N, s2_3a, s2_3b⟩ := s2_2
    -- 2.4. instantiate n := N + 1 in line 2.3
    have r303_1 : (N : ℝ) + 1 ≥ (N : ℝ) := by parley_order
    have s2_4 : abs (1 / ((N : ℝ) + 1) - 1) < 1 / 2 := by first | linarith [(s2_3b (N + 1) (by parley_side) (by parley_side))] | (have h := (s2_3b (N + 1) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s2_3b (N + 1) (by parley_side) (by parley_side)) | (have h := (s2_3b (N + 1) (by parley_side) (by parley_side)); parley_side)
    -- 2.5. inequalities, from 2.3
    have s2_5 : (N : ℝ) + 1 > 0 := by parley_order
    -- 2.6. mun:abs-difference-lt x := 1/(N + 1), c := 1, δ := 1/2, from 2.4
    have s2_6 : 1 - 1 / 2 < 1 / ((N : ℝ) + 1) ∧ 1 / ((N : ℝ) + 1) < 1 + 1 / 2 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := 1 / ((N : ℝ) + 1)) (c := (1 : ℝ)) (δ := (1 / 2 : ℝ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := 1 / ((N : ℝ) + 1)) (c := (1 : ℝ)) (δ := (1 / 2 : ℝ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := 1 / ((N : ℝ) + 1)) (c := (1 : ℝ)) (δ := (1 / 2 : ℝ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := 1 / ((N : ℝ) + 1)) (c := (1 : ℝ)) (δ := (1 / 2 : ℝ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := 1 / ((N : ℝ) + 1)) (c := (1 : ℝ)) (δ := (1 / 2 : ℝ)))).mp (by parley_side); parley_side)
    -- 2.7. inequalities, from 2.3
    have s2_7 : 2 ≤ (N : ℝ) + 1 := by parley_order
    -- 2.8. mun:reciprocal-order x := 2, y := N + 1, from 2.7
    have r316_1 : (2 : ℝ) > 0 := by parley_arith
    have r316_2 : (N : ℝ) + 1 > 0 := by parley_side
    have s2_8 : 1 / ((N : ℝ) + 1) ≤ 1 / 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (2 : ℝ)) (by parley_side) (y := (N : ℝ) + 1) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (2 : ℝ)) (by parley_side) (y := (N : ℝ) + 1) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (2 : ℝ)) (by parley_side) (y := (N : ℝ) + 1) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (2 : ℝ)) (by parley_side) (y := (N : ℝ) + 1) (by parley_side))).mp (by parley_side); parley_side)
    -- 2.9. inequalities, from 2.6
    have s2_9 : ¬ 1 / ((N : ℝ) + 1) ≤ 1 / 2 := by parley_side
    all_goals parley_side
  all_goals exact s2

end Parley.Tests.Notations.Calculus.OneOverNDoesNotTendToOne

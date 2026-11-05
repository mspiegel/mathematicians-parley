module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums
public import Parley.Stdlib.Calculus.FirstTermsBounded

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.ConvergentAbsBounded

set_option maxHeartbeats 400000 in
theorem convergent_abs_bounded (x : ℤ → ℝ) (L : ℝ) (hH3 : Filter.Tendsto (fun n : ℕ => (x (n : ℤ) : ℝ)) Filter.atTop (nhds L)) :
    (∃ B : ℝ, ∀ m : ℕ, 0 < m → abs (x (m : ℤ)) ≤ B) := by
  -- 1. def:tends-to, from H3
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (x (n : ℤ) - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side); parley_side)
  -- 2. instantiate ε := 1 in line 1
  have r583_1 : (0 : ℝ) < 1 := by parley_arith
  have s2 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (x (n : ℤ) - L) < 1) := by first | exact (s1 (1 : ℝ) (by parley_side)) | exact ((s1 (1 : ℝ) (by parley_side))).symm | simpa using (s1 (1 : ℝ) (by parley_side)) | exact_mod_cast (s1 (1 : ℝ) (by parley_side)) | (have h := (s1 (1 : ℝ) (by parley_side)); parley_side)
  -- 3. obtain N from line 2
  obtain ⟨N, s3a, s3b⟩ := s2
  try lift N to ℕ using le_of_lt s3a
  -- 4. mun:first-terms-bounded
  have s4 : ∀ K : ℕ, 0 < K → (∃ C : ℝ, ∀ m : ℤ, m ∈ Finset.Icc 1 (K : ℤ) → abs (x m) ≤ C) := by first | exact (Parley.Stdlib.Calculus.FirstTermsBounded.first_terms_bounded (x := x)) | exact ((Parley.Stdlib.Calculus.FirstTermsBounded.first_terms_bounded (x := x))).symm | simpa using (Parley.Stdlib.Calculus.FirstTermsBounded.first_terms_bounded (x := x)) | exact_mod_cast (Parley.Stdlib.Calculus.FirstTermsBounded.first_terms_bounded (x := x)) | (have h := (Parley.Stdlib.Calculus.FirstTermsBounded.first_terms_bounded (x := x)); parley_side)
  -- 5. instantiate K := N in line 4
  have s5 : ∃ C : ℝ, ∀ i : ℤ, i ∈ Finset.Icc 1 (N : ℤ) → abs (x i) ≤ C := by first | exact (s4 N (by parley_side)) | exact ((s4 N (by parley_side))).symm | simpa using (s4 N (by parley_side)) | exact_mod_cast (s4 N (by parley_side)) | (have h := (s4 N (by parley_side)); parley_side)
  -- 6. obtain C from line 5
  obtain ⟨C, s6⟩ := s5
  -- 7. membership
  set B : ℝ := max C (abs L + 1) with hD1
  -- 8. mun:le-max x := C, y := |L| + 1, from D1
  have s8 : C ≤ B := by
    try simp only [hD1] at *
    try push_cast at *
    first | linarith [(Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := C) (y := abs L + 1))] | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := C) (y := abs L + 1)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := C) (y := abs L + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := C) (y := abs L + 1)); parley_side)
  -- 9. mun:le-max x := C, y := |L| + 1, from D1
  have s9 : abs L + 1 ≤ B := by
    try simp only [hD1] at *
    try push_cast at *
    first | linarith [(Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := C) (y := abs L + 1))] | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := C) (y := abs L + 1)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := C) (y := abs L + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := C) (y := abs L + 1)); parley_side)
  -- 10. proof
  have s10 : ∀ m : ℕ, 0 < m → abs (x (m : ℤ)) ≤ B := by
    intro m hK1
    -- 10.1. mun:abs-real x := x(m), from H1
    -- 10.2. axi:excluded-middle P := m ≤ N
    have s10_2 : (m : ℝ) ≤ (N : ℝ) ∨ ¬ (m : ℝ) ≤ (N : ℝ) := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (m : ℝ) ≤ (N : ℝ))) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (m : ℝ) ≤ (N : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (m : ℝ) ≤ (N : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (m : ℝ) ≤ (N : ℝ))) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (m : ℝ) ≤ (N : ℝ))); parley_side)
    -- 10.3. cases, from 10.2
    have s10_3 : abs (x (m : ℤ)) ≤ B := by
      rcases s10_2 with hC1 | hC2
      · skip
        -- 10.3.1. def:range n := N, k := m, from C1
        have s10_3_1 : (m : ℤ) ∈ Finset.Icc (1 : ℤ) (N : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range (k := (m : ℤ)) (n := (N : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range (k := (m : ℤ)) (n := (N : ℤ)))).mpr (by parley_side); parley_side)
        -- 10.3.2. instantiate i := m in line 6, from 10.3.1
        have s10_3_2 : abs (x (m : ℤ)) ≤ C := by first | linarith [(s6 (m : ℤ) (by parley_side))] | (have h := (s6 (m : ℤ) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s6 (m : ℤ) (by parley_side)) | (have h := (s6 (m : ℤ) (by parley_side)); parley_side)
        -- 10.3.3. transitivity, from 10.3.2, 8
        have s10_3_3 : abs (x (m : ℤ)) ≤ B := by parley_order
        all_goals parley_side
      · skip
        -- 10.3.4. inequalities, from C2
        have s10_3_4 : (N : ℝ) < (m : ℝ) := by parley_order
        -- 10.3.5. inequalities
        have s10_3_5 : (m : ℝ) ≥ (N : ℝ) := by parley_order
        -- 10.3.6. instantiate n := m in line 3, from 10.3.5
        have s10_3_6 : abs (x (m : ℤ) - L) < 1 := by first | linarith [(s3b m (by parley_side) (by parley_side))] | (have h := (s3b m (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s3b m (by parley_side) (by parley_side)) | (have h := (s3b m (by parley_side) (by parley_side)); parley_side)
        -- 10.3.7. thm:triangle-inequality a := x(m) − L, b := L
        have s10_3_7 : abs (x (m : ℤ) - L + L) ≤ abs (x (m : ℤ) - L) + abs L := by first | linarith [(Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := x (m : ℤ) - L) (b := L))] | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := x (m : ℤ) - L) (b := L)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := x (m : ℤ) - L) (b := L)) | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := x (m : ℤ) - L) (b := L)); parley_side)
        -- 10.3.8. substitute
        have s10_3_8 : abs (x (m : ℤ)) ≤ abs (x (m : ℤ) - L) + abs L := by
          have c1 : x (m : ℤ) - L + L = x (m : ℤ) := by parley_ring
          have row1 : abs (x (m : ℤ)) ≤ abs (x (m : ℤ) - L) + abs L := by parley_subst_at c1 s10_3_7
          exact row1
        -- 10.3.9. inequalities
        have s10_3_9 : abs (x (m : ℤ) - L) + abs L < abs L + 1 := by parley_order
        -- 10.3.10. transitivity, from 10.3.8, 10.3.9
        have s10_3_10 : abs (x (m : ℤ)) < abs L + 1 := by parley_order
        -- 10.3.11. transitivity, from 10.3.10, 9
        have s10_3_11 : abs (x (m : ℤ)) < B := by parley_order
        -- 10.3.12. inequalities
        have s10_3_12 : abs (x (m : ℤ)) ≤ B := by parley_order
        all_goals parley_side
    all_goals exact s10_3
  -- 11. exhibit, from 10
  have s11 : ∃ B : ℝ, ∀ m : ℕ, 0 < m → abs (x (m : ℤ)) ≤ B := ⟨B, by parley_side⟩
  all_goals exact s11

end Parley.Stdlib.Calculus.ConvergentAbsBounded

module

public import OrderTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.FirstTermsBounded

theorem first_terms_bounded (x : ℤ → ℝ) :
    (∀ K : ℕ, 0 < K → (∃ C : ℝ, ∀ m : ℤ, m ∈ Finset.Icc 1 (K : ℤ) → abs (x m) ≤ C)) := by
  -- 1. induction on K starting at 1
  have s1 : ∀ K : ℕ, 0 < K → (∃ C : ℝ, ∀ m : ℤ, m ∈ Finset.Icc 1 (K : ℤ) → abs (x m) ≤ C) := by
    intro K h_K
    replace h_K : 1 ≤ K := h_K
    induction K, h_K using Nat.le_induction with
    | base =>
      -- 1.1. mun:abs-real x := x(1)
      -- 1.2. proof
      have s1_2 : ∀ m : ℤ, m ∈ Finset.Icc 1 1 → abs (x m) ≤ abs (x 1) := by
        intro m hK1
        try have hK1_bounds := Finset.mem_Icc.mp hK1
        -- 1.2.1. def:range n := 1, k := m, from K1
        have s1_2_1 : 0 < m ∧ m ≤ 1 := by first | exact ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (1 : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (1 : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (1 : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (1 : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (1 : ℤ)))).mp (by parley_side); parley_side)
        -- 1.2.2. inequalities, from 1.2.1
        have s1_2_2 : m ≤ 1 := by parley_order
        -- 1.2.3. inequalities, from K1
        have s1_2_3 : 1 ≤ m := by parley_order
        -- 1.2.4. antisymmetry, from 1.2.2, 1.2.3
        have s1_2_4 : m = 1 := by parley_side
        -- 1.2.5. substitute m = 1 (line 1.2.4)
        have s1_2_5 : abs (x m) = abs (x 1) := by
          have s1_2_4_w : (m : ℝ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s1_2_4; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s1_2_4_w | parley_subst s1_2_4
        -- 1.2.6. inequalities
        have s1_2_6 : abs (x m) ≤ abs (x 1) := by parley_order
        all_goals exact s1_2_6
      -- 1.3. exhibit, from 1.1, 1.2
      have s1_3 : ∃ C : ℝ, ∀ m : ℤ, m ∈ Finset.Icc 1 1 → abs (x m) ≤ C := ⟨abs (x 1), by parley_side⟩
      all_goals parley_side
    | succ K hK hIH =>
      -- 1.4. obtain C from IH
      obtain ⟨C, s1_4⟩ := hIH
      -- 1.5. mun:abs-real x := x(K + 1)
      set E : ℝ := max C (abs (x ((K : ℤ) + 1))) with hD
      -- 1.6. mun:le-max x := C, y := |x(K + 1)|, from D, 1.5
      have s1_6 : C ≤ E := by
        try simp only [hD] at *
        try push_cast at *
        first | linarith [(Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := C) (y := abs (x ((K : ℤ) + 1))))] | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := C) (y := abs (x ((K : ℤ) + 1)))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := C) (y := abs (x ((K : ℤ) + 1)))) | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := C) (y := abs (x ((K : ℤ) + 1)))); parley_side)
      -- 1.7. mun:le-max x := C, y := |x(K + 1)|, from D, 1.5
      have s1_7 : abs (x ((K : ℤ) + 1)) ≤ E := by
        try simp only [hD] at *
        try push_cast at *
        first | linarith [(Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := C) (y := abs (x ((K : ℤ) + 1))))] | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := C) (y := abs (x ((K : ℤ) + 1)))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := C) (y := abs (x ((K : ℤ) + 1)))) | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := C) (y := abs (x ((K : ℤ) + 1)))); parley_side)
      -- 1.8. proof
      have s1_8 : ∀ m : ℤ, m ∈ Finset.Icc 1 ((K : ℤ) + 1) → abs (x m) ≤ E := by
        intro m hK2
        try have hK2_bounds := Finset.mem_Icc.mp hK2
        -- 1.8.1. def:range n := K + 1, k := m, from K2
        have s1_8_1 : 0 < m ∧ m ≤ (K : ℤ) + 1 := by first | exact ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (K : ℤ) + 1))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (K : ℤ) + 1))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (K : ℤ) + 1))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (K : ℤ) + 1))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (K : ℤ) + 1))).mp (by parley_side); parley_side)
        -- 1.8.2. mun:le-cases x := m, y := K + 1, from 1.8.1
        have s1_8_2 : m < (K : ℤ) + 1 ∨ m = (K : ℤ) + 1 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := m) (y := (K : ℤ) + 1))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_le_cases (x := m) (y := (K : ℤ) + 1))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := m) (y := (K : ℤ) + 1))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := m) (y := (K : ℤ) + 1))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := m) (y := (K : ℤ) + 1))).mp (by parley_side); parley_side)
        -- 1.8.3. mun:abs-real x := x(m), from H1
        -- 1.8.4. cases, from 1.8.2
        have s1_8_4 : abs (x m) ≤ E := by
          rcases s1_8_2 with hC1 | hC2
          · skip
            -- 1.8.4.1. mun:integer-step n := K + 1, from C1
            have s1_8_4_1 : m + 1 ≤ (K : ℤ) + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := (K : ℤ) + 1) hC1)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := (K : ℤ) + 1) hC1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := (K : ℤ) + 1) hC1) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := (K : ℤ) + 1) hC1); parley_side)
            -- 1.8.4.2. inequalities
            have s1_8_4_2 : m ≤ (K : ℤ) := by parley_order
            -- 1.8.4.3. def:range n := K, k := m, from 1.8.4.2
            have s1_8_4_3 : m ∈ Finset.Icc (1 : ℤ) (K : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (K : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (K : ℤ)))).mpr (by parley_side); parley_side)
            -- 1.8.4.4. instantiate i := m in line 1.4, from 1.8.4.3
            have s1_8_4_4 : abs (x m) ≤ C := by first | linarith [(s1_4 m (by parley_side))] | (have h := (s1_4 m (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1_4 m (by parley_side)) | (have h := (s1_4 m (by parley_side)); parley_side)
            -- 1.8.4.5. transitivity, from 1.8.4.4, 1.6
            have s1_8_4_5 : abs (x m) ≤ E := by parley_order
            all_goals parley_side
          · skip
            -- 1.8.4.6. substitute m = K + 1 (C2)
            have s1_8_4_6 : abs (x m) = abs (x ((K : ℤ) + 1)) := by
              have hC2_w : (m : ℝ) = (K : ℝ) + 1 := by have h := congrArg (fun x : ℤ => (x : ℝ)) hC2; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst hC2_w | parley_subst hC2
            -- 1.8.4.7. transitivity, from 1.8.4.6, 1.7
            have s1_8_4_7 : abs (x m) ≤ E := by parley_order
            all_goals parley_side
        all_goals exact s1_8_4
      -- 1.9. exhibit, from 1.8
      have s1_9 : ∃ C : ℝ, ∀ m : ℤ, m ∈ Finset.Icc 1 ((K : ℤ) + 1) → abs (x m) ≤ C := ⟨E, by parley_side⟩
      all_goals parley_side
  all_goals exact s1

end Parley.Stdlib.Calculus.FirstTermsBounded

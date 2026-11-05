module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Proofs.Wiedijk.PerfectNumbers
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/perfect-numbers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PerfectNumbers.OddPart

theorem odd_part (n : ℕ) (hH1 : 0 < n) :
    (∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ (n : ℤ) = 2 ^ k * (m : ℤ))) := by
  -- 1. induction on N starting at 0
  have s1 : ∀ N : ℕ, ∀ j : ℤ, j ∈ Finset.Icc 1 (N : ℤ) → (∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ j = 2 ^ k * (m : ℤ))) := by
    intro N
    induction N with
    | zero =>
      intro j hK1
      try push_cast at hK1
      try have hK1_bounds := Finset.mem_Icc.mp hK1
      -- 1.1. mun:range-bounds a := 1, b := 0, k := j, from K1
      have s1_1 : 1 ≤ j := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (0 : ℤ)) (k := j) hK1)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (0 : ℤ)) (k := j) hK1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (0 : ℤ)) (k := j) hK1) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (0 : ℤ)) (k := j) hK1); parley_side)
      -- 1.2. mun:range-bounds a := 1, b := 0, k := j, from K1
      have s1_2 : j ≤ 0 := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (0 : ℤ)) (k := j) hK1)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (0 : ℤ)) (k := j) hK1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (0 : ℤ)) (k := j) hK1) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (0 : ℤ)) (k := j) hK1); parley_side)
      -- 1.3. inequalities, from 1.1
      have s1_3 : ¬ j ≤ 0 := by parley_side
      all_goals parley_side
    | succ N hIH =>
      intro j hK3
      try push_cast at hK3
      try have hK3_bounds := Finset.mem_Icc.mp hK3
      -- 1.4. mun:range-bounds a := 1, b := N + 1, k := j, from K3
      have s1_4 : 1 ≤ j := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (N : ℤ) + 1) (k := j) hK3)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (N : ℤ) + 1) (k := j) hK3); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (N : ℤ) + 1) (k := j) hK3) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (N : ℤ) + 1) (k := j) hK3); parley_side)
      -- 1.5. mun:range-bounds a := 1, b := N + 1, k := j, from K3
      have s1_5 : j ≤ (N : ℤ) + 1 := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (N : ℤ) + 1) (k := j) hK3)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (N : ℤ) + 1) (k := j) hK3); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (N : ℤ) + 1) (k := j) hK3) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (N : ℤ) + 1) (k := j) hK3); parley_side)
      -- 1.6. mun:even-or-odd n := j
      have s1_6 : Even j ∨ Odd j := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := j)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := j))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := j)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := j)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := j)); parley_side)
      -- 1.7. cases, from 1.6
      have s1_7 : ∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ j = 2 ^ k * (m : ℤ)) := by
        rcases s1_6 with hC1 | hC2
        · skip
          -- 1.7.1. obtain i: def:even n := j, from C1
          obtain ⟨i, s1_7_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := j))).mp (by parley_side)
          -- 1.7.2. substitute j = 2i (line 1.7.1) into line 1.4
          have s1_7_2 : 1 ≤ 2 * i := by parley_subst_at s1_7_1 s1_4
          -- 1.7.3. mun:factor-positive a := 2, b := i
          have r197_1 : (2 : ℤ) ≥ 0 := by parley_arith
          have r197_2 : 2 * i > 0 := by parley_order
          have s1_7_3 : 0 < i := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_factor_positive (a := (2 : ℤ)) (b := i) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := (2 : ℤ)) (b := i) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := (2 : ℤ)) (b := i) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := (2 : ℤ)) (b := i) (by parley_side) (by parley_side)); parley_side)
          -- 1.7.4. mun:pos-int-nat m := i, from 1.7.3
          have s1_7_4 : 0 < i := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := i) s1_7_3) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := i) s1_7_3)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := i) s1_7_3) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := i) s1_7_3) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := i) s1_7_3); parley_side)
          lift i to ℕ using s1_7_4.le
          -- 1.7.5. inequalities
          have s1_7_5 : (i : ℤ) < 2 * (i : ℤ) := by parley_order
          -- 1.7.6. transitivity, from 1.7.5, 1.7.1, 1.5
          have s1_7_6 : (i : ℤ) < (N : ℤ) + 1 := by parley_order
          -- 1.7.7. mun:integer-step m := i, n := N + 1, from 1.7.6
          have s1_7_7 : (i : ℤ) + 1 ≤ (N : ℤ) + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (i : ℤ)) (n := (N : ℤ) + 1) s1_7_6)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (i : ℤ)) (n := (N : ℤ) + 1) s1_7_6); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (i : ℤ)) (n := (N : ℤ) + 1) s1_7_6) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (i : ℤ)) (n := (N : ℤ) + 1) s1_7_6); parley_side)
          -- 1.7.8. inequalities
          have s1_7_8 : (i : ℤ) ≤ (N : ℤ) := by parley_order
          -- 1.7.9. def:range-between k := i, a := 1, b := N, from 1.7.8
          have r222_1 : 1 ≤ (i : ℤ) := by parley_order
          have s1_7_9 : (i : ℤ) ∈ Finset.Icc (1 : ℤ) (N : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := (i : ℤ)) (a := (1 : ℤ)) (b := (N : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := (i : ℤ)) (a := (1 : ℤ)) (b := (N : ℤ)))).mpr (by parley_side); parley_side)
          -- 1.7.10. instantiate j := i in IH, from 1.7.9
          have s1_7_10 : ∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ (i : ℤ) = 2 ^ k * (m : ℤ)) := by first | exact (hIH (i : ℤ) (by parley_side)) | exact ((hIH (i : ℤ) (by parley_side))).symm | simpa using (hIH (i : ℤ) (by parley_side)) | exact_mod_cast (hIH (i : ℤ) (by parley_side)) | (have h := (hIH (i : ℤ) (by parley_side)); parley_side)
          -- 1.7.11. D1, from 1.7.10
          have s1_7_11 : ∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ (i : ℤ) = 2 ^ k * (m : ℤ)) := by parley_side
          -- 1.7.12. obtain k, m from line 1.7.11
          obtain ⟨k, m, s1_7_12a, ⟨s1_7_12b, s1_7_12c⟩⟩ := s1_7_11
          try lift m to ℕ using le_of_lt s1_7_12a
          -- 1.7.13. mun:exponent-step a := 2, m := k
          have s1_7_13 : (2 ^ (k + 1) : ℤ) = 2 ^ k * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); parley_side)
          -- 1.7.14. algebra, from 1.7.1, 1.7.12, 1.7.13
          have s1_7_14 : j = 2 ^ (k + 1) * (m : ℤ) := by linear_combination (norm := parley_norm) s1_7_1 + (2) * s1_7_12c + (-(m : ℤ)) * s1_7_13
          -- 1.7.15. exhibit, from 1.7.12, 1.7.14
          have s1_7_15 : ∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ j = 2 ^ k * (m : ℤ)) := ⟨k + 1, m, by parley_side, ⟨by parley_side, by parley_side⟩⟩
          all_goals parley_side
        · skip
          -- 1.7.16. algebra
          have s1_7_16 : j = 2 ^ 0 * j := by parley_ring
          -- 1.7.17. exhibit, from C2, 1.7.16
          have s1_7_17 : ∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ j = 2 ^ k * (m : ℤ)) := ⟨0, j.toNat, by (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ j by parley_side)]); (try push_cast); parley_side, ⟨by (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ j by parley_side)]); (try push_cast); parley_side, by (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ j by parley_side)]); (try push_cast); parley_side⟩⟩
          all_goals parley_side
      -- 1.8. D1, from 1.7
      have s1_8 : ∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ j = 2 ^ k * (m : ℤ)) := by parley_side
      all_goals parley_side
  -- 2. instantiate N := n in line 1
  have s2 : ∀ j : ℤ, j ∈ Finset.Icc 1 (n : ℤ) → (∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ j = 2 ^ k * (m : ℤ))) := by intro j h_j; first | exact (s1 n j (by parley_side)) | exact ((s1 n j (by parley_side))).symm | simpa using (s1 n j (by parley_side)) | exact_mod_cast (s1 n j (by parley_side)) | (have h := (s1 n j (by parley_side)); parley_side)
  -- 3. def:range-between k := n, a := 1, b := n
  have r260_1 : 1 ≤ (n : ℤ) := by parley_order
  have r260_2 : (n : ℤ) ≤ (n : ℤ) := by parley_order
  have s3 : (n : ℤ) ∈ Finset.Icc (1 : ℤ) (n : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := (n : ℤ)) (a := (1 : ℤ)) (b := (n : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := (n : ℤ)) (a := (1 : ℤ)) (b := (n : ℤ)))).mpr (by parley_side); parley_side)
  -- 4. instantiate j := n in line 2, from 3
  have s4 : ∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ (n : ℤ) = 2 ^ k * (m : ℤ)) := by first | exact (s2 (n : ℤ) (by parley_side)) | exact ((s2 (n : ℤ) (by parley_side))).symm | simpa using (s2 (n : ℤ) (by parley_side)) | exact_mod_cast (s2 (n : ℤ) (by parley_side)) | (have h := (s2 (n : ℤ) (by parley_side)); parley_side)
  -- 5. D1, from 4
  have s5 : ∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ (n : ℤ) = 2 ^ k * (m : ℤ)) := by parley_side
  all_goals exact s5

end Parley.Proofs.Wiedijk.PerfectNumbers.OddPart

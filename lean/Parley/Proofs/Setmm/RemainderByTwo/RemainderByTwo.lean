module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/remainder-by-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderByTwo.RemainderByTwo

theorem remainder_by_two (N : ℤ) :
    (N % (2 : ℤ) = 1 ↔ ¬ (2 : ℤ) ∣ N) := by
  -- the theorem. both directions
  have sThm : N % (2 : ℤ) = 1 ↔ ¬ (2 : ℤ) ∣ N := by
    constructor
    · skip
      intro hD1
      -- 1. obtain q: mun:mod-remainder a := N, m := 2, r := 1, from D1
      have r18_1 : (1 : ℤ) < 2 := by parley_arith
      obtain ⟨q, s1⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := N) (m := 2) (by parley_side) (r := 1) (by parley_side))).mp (by parley_side)
      -- 2. algebra, from 1
      have s2 : N = 2 * q + 1 := by linear_combination (norm := parley_norm) (-1) * s1
      -- 3. def:odd n := N, from 2
      have s3 : Odd N := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mpr ⟨q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mpr ⟨q, by parley_side⟩; parley_side)
      -- 4. contradiction
      have s4 : ¬ (2 : ℤ) ∣ N := by
        by_contra hc_hS1
        have hS1 : (2 : ℤ) ∣ N := by parley_suppose hc_hS1
        -- 4.1. obtain k: def:divides d := 2, n := N, from S1
        obtain ⟨k, s4_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := N))).mp (by parley_side)
        -- 4.2. def:even n := N, from 4.1
        have s4_2 : Even N := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := N))).mpr ⟨k, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := N))).mpr ⟨k, by parley_side⟩; parley_side)
        -- 4.3. mun:not-both n := N, from 4.2
        have s4_3 : ¬ Odd N := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := N) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := N) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := N) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := N) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := N) (by parley_side)); parley_side)
        all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 5. contradiction
      have s5 : ¬ Even N := by
        by_contra hc_hS2
        have hS2 : Even N := by parley_suppose hc_hS2
        -- 5.1. obtain k: def:even n := N, from S2
        obtain ⟨k, s5_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := N))).mp (by parley_side)
        -- 5.2. def:divides d := 2, n := N, from 5.1
        have s5_2 : (2 : ℤ) ∣ N := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := N))).mpr ⟨k, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := N))).mpr ⟨k, by parley_side⟩; parley_side)
        all_goals parley_side
      -- 6. mun:even-or-odd
      have s6 : Even N ∨ Odd N := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := N)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := N))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := N)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := N)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := N)); parley_side)
      -- 7. mun:disjunctive-syllogism-left P := N is even, Q := N is odd, from 5, 6
      have s7 : Odd N := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even N) (Q := Odd N) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even N) (Q := Odd N) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even N) (Q := Odd N) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even N) (Q := Odd N) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even N) (Q := Odd N) (by parley_side) (by parley_side)); parley_side)
      -- 8. obtain k: def:odd, from 7
      obtain ⟨k, s8⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mp (by parley_side)
      -- 9. algebra, from 8
      have s9 : k * 2 + 1 = N := by linear_combination (norm := parley_norm) (-1) * s8
      -- 10. exhibit, from 9
      have s10 : ∃ q : ℤ, q * 2 + 1 = N := ⟨k, by parley_side⟩
      -- 11. mun:mod-remainder a := N, m := 2, r := 1, from 10
      have r69_1 : (1 : ℤ) < 2 := by parley_arith
      have s11 : N % (2 : ℤ) = 1 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := N) (m := 2) (by parley_side) (r := 1) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := N) (m := 2) (by parley_side) (r := 1) (by parley_side))).mpr (by parley_side); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.RemainderByTwo.RemainderByTwo

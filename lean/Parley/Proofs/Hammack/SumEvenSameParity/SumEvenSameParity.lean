module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/sum-even-same-parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumEvenSameParity.SumEvenSameParity

theorem sum_even_same_parity (x : ℤ) (y : ℤ) (hH3 : Even (x + y)) :
    (Even x ∧ Even y ∨ Odd x ∧ Odd y) := by
  -- 1. mun:even-or-odd n := x
  have s1 : Even x ∨ Odd x := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)); parley_side)
  -- 2. mun:even-or-odd n := y
  have s2 : Even y ∨ Odd y := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y)); parley_side)
  -- 3. cases, from 1
  have s3 : Even x ∧ Even y ∨ Odd x ∧ Odd y := by
    rcases s1 with hC1 | hC4
    · skip
      -- 3.1. obtain a: def:even n := x, from C1
      obtain ⟨a, s3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := x))).mp (by parley_side)
      -- 3.2. cases, from 2
      have s3_2 : Even x ∧ Even y ∨ Odd x ∧ Odd y := by
        rcases s2 with hC2 | hC3
        · skip
          -- 3.2.1. join C1, C2
          have s3_2_1 : Even x ∧ Even y := by parley_side
          -- 3.2.2. mun:or-left P := x is even and y is even, Q := x is odd and y is odd, from 3.2.1
          have s3_2_2 : Even x ∧ Even y ∨ Odd x ∧ Odd y := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) (by parley_side)); parley_side)
          all_goals parley_side
        · skip
          -- 3.2.3. obtain b: def:odd n := y, from C3
          obtain ⟨b, s3_2_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := y))).mp (by parley_side)
          -- 3.2.4. algebra, from 3.1, 3.2.3
          have s3_2_4 : x + y = 2 * (a + b) + 1 := by linear_combination (norm := parley_norm) s3_1 + s3_2_3
          -- 3.2.5. def:odd n := x + y, from 3.2.4
          have s3_2_5 : Odd (x + y) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := x + y))).mpr ⟨a + b, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x + y))).mpr ⟨a + b, by parley_side⟩; parley_side)
          -- 3.2.6. mun:not-both n := x + y, from H3
          have s3_2_6 : ¬ Odd (x + y) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) (by parley_side)); parley_side)
          all_goals parley_side
      all_goals parley_side
    · skip
      -- 3.3. obtain a: def:odd n := x, from C4
      obtain ⟨a, s3_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x))).mp (by parley_side)
      -- 3.4. cases, from 2
      have s3_4 : Even x ∧ Even y ∨ Odd x ∧ Odd y := by
        rcases s2 with hC5 | hC6
        · skip
          -- 3.4.1. obtain b: def:even n := y, from C5
          obtain ⟨b, s3_4_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := y))).mp (by parley_side)
          -- 3.4.2. algebra, from 3.3, 3.4.1
          have s3_4_2 : x + y = 2 * (a + b) + 1 := by linear_combination (norm := parley_norm) s3_3 + s3_4_1
          -- 3.4.3. def:odd n := x + y, from 3.4.2
          have s3_4_3 : Odd (x + y) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := x + y))).mpr ⟨a + b, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x + y))).mpr ⟨a + b, by parley_side⟩; parley_side)
          -- 3.4.4. mun:not-both n := x + y, from H3
          have s3_4_4 : ¬ Odd (x + y) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) (by parley_side)); parley_side)
          all_goals parley_side
        · skip
          -- 3.4.5. join C4, C6
          have s3_4_5 : Odd x ∧ Odd y := by parley_side
          -- 3.4.6. mun:or-right P := x is even and y is even, Q := x is odd and y is odd, from 3.4.5
          have s3_4_6 : Even x ∧ Even y ∨ Odd x ∧ Odd y := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) (by parley_side)); parley_side)
          all_goals parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.SumEvenSameParity.SumEvenSameParity

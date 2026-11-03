module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/three-naturals-two-same-parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ThreeNaturalsTwoSameParity.ThreeNaturalsTwoSameParity

theorem three_naturals_two_same_parity (a : ℕ) (hH1 : 0 < a) (b : ℕ) (hH2 : 0 < b) (c : ℕ) (hH3 : 0 < c) :
    ((Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) ∨ Even ((b : ℤ) - (c : ℤ))) := by
  -- 1. mun:even-or-odd n := a − b
  have s1 : Even ((a : ℤ) - (b : ℤ)) ∨ Odd ((a : ℤ) - (b : ℤ)) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ) - (b : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ) - (b : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ) - (b : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ) - (b : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ) - (b : ℤ))); parley_side)
  -- 2. cases, from 1
  have s2 : (Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) ∨ Even ((b : ℤ) - (c : ℤ)) := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. mun:or-left P := a − b is even, Q := a + c is even, from C1
      have s2_1 : Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ)) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ))) (Q := Even ((a : ℤ) + (c : ℤ))) hC1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ))) (Q := Even ((a : ℤ) + (c : ℤ))) hC1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ))) (Q := Even ((a : ℤ) + (c : ℤ))) hC1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ))) (Q := Even ((a : ℤ) + (c : ℤ))) hC1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ))) (Q := Even ((a : ℤ) + (c : ℤ))) hC1); parley_side)
      -- 2.2. mun:or-left P := a − b is even or a + c is even, Q := b − c is even, from 2.1
      have s2_2 : (Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) ∨ Even ((b : ℤ) - (c : ℤ)) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) s2_1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) s2_1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) s2_1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) s2_1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) s2_1); parley_side)
      all_goals parley_side
    · skip
      -- 2.3. mun:even-or-odd n := a + c
      have s2_3 : Even ((a : ℤ) + (c : ℤ)) ∨ Odd ((a : ℤ) + (c : ℤ)) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ) + (c : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ) + (c : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ) + (c : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ) + (c : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ) + (c : ℤ))); parley_side)
      -- 2.4. cases, from 2.3
      have s2_4 : (Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) ∨ Even ((b : ℤ) - (c : ℤ)) := by
        rcases s2_3 with hC3 | hC4
        · skip
          -- 2.4.1. mun:or-right P := a − b is even, Q := a + c is even, from C3
          have s2_4_1 : Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ)) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even ((a : ℤ) - (b : ℤ))) (Q := Even ((a : ℤ) + (c : ℤ))) hC3) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even ((a : ℤ) - (b : ℤ))) (Q := Even ((a : ℤ) + (c : ℤ))) hC3)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even ((a : ℤ) - (b : ℤ))) (Q := Even ((a : ℤ) + (c : ℤ))) hC3) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even ((a : ℤ) - (b : ℤ))) (Q := Even ((a : ℤ) + (c : ℤ))) hC3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even ((a : ℤ) - (b : ℤ))) (Q := Even ((a : ℤ) + (c : ℤ))) hC3); parley_side)
          -- 2.4.2. mun:or-left P := a − b is even or a + c is even, Q := b − c is even, from 2.4.1
          have s2_4_2 : (Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) ∨ Even ((b : ℤ) - (c : ℤ)) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) s2_4_1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) s2_4_1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) s2_4_1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) s2_4_1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) s2_4_1); parley_side)
          all_goals parley_side
        · skip
          -- 2.4.3. mun:even-or-odd n := b − c
          have s2_4_3 : Even ((b : ℤ) - (c : ℤ)) ∨ Odd ((b : ℤ) - (c : ℤ)) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ) - (c : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ) - (c : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ) - (c : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ) - (c : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ) - (c : ℤ))); parley_side)
          -- 2.4.4. cases, from 2.4.3
          have s2_4_4 : (Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) ∨ Even ((b : ℤ) - (c : ℤ)) := by
            rcases s2_4_3 with hC5 | hC6
            · skip
              -- 2.4.4.1. mun:or-right P := a − b is even or a + c is even, Q := b − c is even, from C5
              have s2_4_4_1 : (Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) ∨ Even ((b : ℤ) - (c : ℤ)) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) hC5) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) hC5)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) hC5) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) hC5) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ))) (Q := Even ((b : ℤ) - (c : ℤ))) hC5); parley_side)
              all_goals parley_side
            · skip
              -- 2.4.4.2. obtain p: def:odd n := a − b, from C2
              obtain ⟨p, s2_4_4_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (a : ℤ) - (b : ℤ)))).mp (by parley_side)
              -- 2.4.4.3. obtain q: def:odd n := a + c, from C4
              obtain ⟨q, s2_4_4_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (a : ℤ) + (c : ℤ)))).mp (by parley_side)
              -- 2.4.4.4. obtain r: def:odd n := b − c, from C6
              obtain ⟨r, s2_4_4_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (b : ℤ) - (c : ℤ)))).mp (by parley_side)
              -- 2.4.4.5. algebra, from 2.4.4.2, 2.4.4.3, 2.4.4.4
              have s2_4_4_5 : 1 = 2 * ((a : ℤ) - p - q - r - 1) := by linear_combination (norm := parley_norm) (-1) * s2_4_4_2 + (-1) * s2_4_4_3 + (-1) * s2_4_4_4
              -- 2.4.4.6. def:even n := 1, from 2.4.4.5
              have s2_4_4_6 : Even (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨(a : ℤ) - p - q - r - 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨(a : ℤ) - p - q - r - 1, by parley_side⟩; parley_side)
              -- 2.4.4.7. mun:not-both n := 1, from 2.4.4.6
              have s2_4_4_7 : ¬ Odd (1 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s2_4_4_6) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s2_4_4_6)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s2_4_4_6) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s2_4_4_6) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s2_4_4_6); parley_side)
              -- 2.4.4.8. arithmetic
              have s2_4_4_8 : Odd (1 : ℤ) := by parley_arith
              all_goals parley_side
          all_goals parley_side
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.ThreeNaturalsTwoSameParity.ThreeNaturalsTwoSameParity

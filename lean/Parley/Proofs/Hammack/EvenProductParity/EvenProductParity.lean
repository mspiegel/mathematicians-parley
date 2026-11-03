module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/even-product-parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.EvenProductParity.EvenProductParity

theorem even_product_parity (x : ℤ) (y : ℤ) (hH3 : Even (x ^ 2 * (y + 3))) :
    (Even x ∨ Odd y) := by
  -- 1. mun:even-or-odd n := x
  have s1 : Even x ∨ Odd x := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)); parley_side)
  -- 2. cases, from 1
  have s2 : Even x ∨ Odd y := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. mun:or-left P := x is even, Q := y is odd, from C1
      have s2_1 : Even x ∨ Odd y := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x) (Q := Odd y) hC1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x) (Q := Odd y) hC1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x) (Q := Odd y) hC1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x) (Q := Odd y) hC1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x) (Q := Odd y) hC1); parley_side)
      all_goals parley_side
    · skip
      -- 2.2. mun:even-or-odd n := y
      have s2_2 : Even y ∨ Odd y := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y)); parley_side)
      -- 2.3. cases, from 2.2
      have s2_3 : Even x ∨ Odd y := by
        rcases s2_2 with hC3 | hC4
        · skip
          -- 2.3.1. obtain a: def:odd n := x, from C2
          obtain ⟨a, s2_3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x))).mp (by parley_side)
          -- 2.3.2. obtain b: def:even n := y, from C3
          obtain ⟨b, s2_3_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := y))).mp (by parley_side)
          -- 2.3.3. calculation
          have s2_3_3 : x ^ 2 * (y + 3) = 2 * (4 * a ^ 2 * b + 6 * a ^ 2 + 4 * a * b + 6 * a + b + 1) + 1 := by
            calc x ^ 2 * (y + 3) = (2 * a + 1) ^ 2 * (y + 3) := by parley_subst s2_3_1
              _ = (2 * a + 1) ^ 2 * (2 * b + 3) := by parley_subst s2_3_2
              _ = 2 * (4 * a ^ 2 * b + 6 * a ^ 2 + 4 * a * b + 6 * a + b + 1) + 1 := by parley_ring
          -- 2.3.4. def:odd n := x²·(y + 3), from 2.3.3
          have s2_3_4 : Odd (x ^ 2 * (y + 3)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := x ^ 2 * (y + 3)))).mpr ⟨4 * a ^ 2 * b + 6 * a ^ 2 + 4 * a * b + 6 * a + b + 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x ^ 2 * (y + 3)))).mpr ⟨4 * a ^ 2 * b + 6 * a ^ 2 + 4 * a * b + 6 * a + b + 1, by parley_side⟩; parley_side)
          -- 2.3.5. mun:not-both n := x²·(y + 3), from H3
          have s2_3_5 : ¬ Odd (x ^ 2 * (y + 3)) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 2 * (y + 3)) hH3) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 2 * (y + 3)) hH3)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 2 * (y + 3)) hH3) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 2 * (y + 3)) hH3) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 2 * (y + 3)) hH3); parley_side)
          all_goals parley_side
        · skip
          -- 2.3.6. mun:or-right P := x is even, Q := y is odd, from C4
          have s2_3_6 : Even x ∨ Odd y := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x) (Q := Odd y) hC4) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x) (Q := Odd y) hC4)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x) (Q := Odd y) hC4) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x) (Q := Odd y) hC4) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x) (Q := Odd y) hC4); parley_side)
          all_goals parley_side
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.EvenProductParity.EvenProductParity

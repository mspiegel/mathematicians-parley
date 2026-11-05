module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/shifted-product-even-iff.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ShiftedProductEvenIff.ShiftedProductEvenIff

set_option maxHeartbeats 400000 in
theorem shifted_product_even_iff (a : ℤ) (b : ℤ) :
    (Even ((a - 3) * b ^ 2) ↔ Odd a ∨ Even b) := by
  -- the theorem. both directions
  have sThm : Even ((a - 3) * b ^ 2) ↔ Odd a ∨ Even b := by
    constructor
    · skip
      intro hD1
      -- 1. mun:even-product-factor n := a − 3, from D1
      have s1 : Even (a - 3) ∨ Even (b ^ 2) := by first | exact ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a - 3) (b := b ^ 2))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a - 3) (b := b ^ 2))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a - 3) (b := b ^ 2))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a - 3) (b := b ^ 2))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a - 3) (b := b ^ 2))).mp (by parley_side); parley_side)
      -- 2. cases, from 1
      have s2 : Odd a ∨ Even b := by
        rcases s1 with hC1 | hC2
        · skip
          -- 2.1. obtain k: def:even n := a − 3, from C1
          obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a - 3))).mp (by parley_side)
          -- 2.2. algebra, from 2.1
          have s2_2 : a = 2 * (k + 1) + 1 := by linear_combination (norm := parley_norm) s2_1
          -- 2.3. def:odd n := a, from 2.2
          have s2_3 : Odd a := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mpr ⟨k + 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mpr ⟨k + 1, by parley_side⟩; parley_side)
          -- 2.4. mun:or-left P := a is odd, Q := b is even, from 2.3
          have s2_4 : Odd a ∨ Even b := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Odd a) (Q := Even b) s2_3) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := Odd a) (Q := Even b) s2_3)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Odd a) (Q := Even b) s2_3) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Odd a) (Q := Even b) s2_3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Odd a) (Q := Even b) s2_3); parley_side)
          all_goals parley_side
        · skip
          -- 2.5. mun:even-or-odd n := b
          have s2_5 : Even b ∨ Odd b := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)); parley_side)
          -- 2.6. cases, from 2.5
          have s2_6 : Even b := by
            rcases s2_5 with hC3 | hC4
            · skip
              all_goals parley_side
            · skip
              -- 2.6.1. obtain k: def:odd n := b, from C4
              obtain ⟨k, s2_6_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := b))).mp (by parley_side)
              -- 2.6.2. algebra, from 2.6.1
              have s2_6_2 : b ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by linear_combination (norm := parley_norm) (b + 2 * k + 1) * s2_6_1
              -- 2.6.3. def:odd n := b², from 2.6.2
              have s2_6_3 : Odd (b ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := b ^ 2))).mpr ⟨2 * k ^ 2 + 2 * k, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := b ^ 2))).mpr ⟨2 * k ^ 2 + 2 * k, by parley_side⟩; parley_side)
              -- 2.6.4. mun:not-both n := b², from C2
              have s2_6_4 : ¬ Odd (b ^ 2) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := b ^ 2) hC2) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := b ^ 2) hC2)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := b ^ 2) hC2) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := b ^ 2) hC2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := b ^ 2) hC2); parley_side)
              all_goals parley_side
          -- 2.7. mun:or-right P := a is odd, Q := b is even, from 2.6
          have s2_7 : Odd a ∨ Even b := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Odd a) (Q := Even b) s2_6) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := Odd a) (Q := Even b) s2_6)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Odd a) (Q := Even b) s2_6) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Odd a) (Q := Even b) s2_6) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Odd a) (Q := Even b) s2_6); parley_side)
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 3. cases, from D2
      have s3 : Even ((a - 3) * b ^ 2) := by
        rcases hD2 with hC5 | hC6
        · skip
          -- 3.1. obtain k: def:odd, from C5
          obtain ⟨k, s3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mp (by parley_side)
          -- 3.2. algebra, from 3.1
          have s3_2 : a - 3 = 2 * (k - 1) := by linear_combination (norm := parley_norm) s3_1
          -- 3.3. def:even n := a − 3, from 3.2
          have s3_3 : Even (a - 3) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := a - 3))).mpr ⟨k - 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := a - 3))).mpr ⟨k - 1, by parley_side⟩; parley_side)
          -- 3.4. mun:even-product a := a − 3, x := b², from 3.3
          have s3_4 : Even ((a - 3) * b ^ 2) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_product (a := a - 3) s3_3 (x := b ^ 2)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_product (a := a - 3) s3_3 (x := b ^ 2))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_product (a := a - 3) s3_3 (x := b ^ 2)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_product (a := a - 3) s3_3 (x := b ^ 2)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_product (a := a - 3) s3_3 (x := b ^ 2)); parley_side)
          all_goals parley_side
        · skip
          -- 3.5. obtain k: def:even, from C6
          obtain ⟨k, s3_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side)
          -- 3.6. algebra, from 3.5
          have s3_6 : (a - 3) * b ^ 2 = 2 * (2 * (a - 3) * k ^ 2) := by linear_combination (norm := parley_norm) (a * b + 2 * a * k - 3 * b - 6 * k) * s3_5
          -- 3.7. def:even n := (a − 3)·b², from 3.6
          have s3_7 : Even ((a - 3) * b ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (a - 3) * b ^ 2))).mpr ⟨2 * (a - 3) * k ^ 2, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (a - 3) * b ^ 2))).mpr ⟨2 * (a - 3) * k ^ 2, by parley_side⟩; parley_side)
          all_goals parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.ShiftedProductEvenIff.ShiftedProductEvenIff

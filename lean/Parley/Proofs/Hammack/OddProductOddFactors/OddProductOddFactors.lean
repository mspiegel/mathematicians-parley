module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/odd-product-odd-factors.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddProductOddFactors.OddProductOddFactors

set_option maxHeartbeats 400000 in
theorem odd_product_odd_factors (a : ℤ) (b : ℤ) (hH3 : Odd (a ^ 2 * (b ^ 2 - 2 * b))) :
    (Odd a ∧ Odd b) := by
  -- 1. mun:even-or-odd n := a
  have s1 : Even a ∨ Odd a := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)); parley_side)
  -- 2. cases, from 1
  have s2 : Odd a := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain m: def:even n := a, from C1
      obtain ⟨m, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp (by parley_side)
      -- 2.2. algebra, from 2.1
      have s2_2 : a ^ 2 * (b ^ 2 - 2 * b) = 2 * (2 * m ^ 2 * (b ^ 2 - 2 * b)) := by linear_combination (norm := parley_norm) (a * b ^ 2 + 2 * b ^ 2 * m - 2 * a * b - 4 * b * m) * s2_1
      -- 2.3. def:even n := a²·(b² − 2b), from 2.2
      have s2_3 : Even (a ^ 2 * (b ^ 2 - 2 * b)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 2 * (b ^ 2 - 2 * b)))).mpr ⟨2 * m ^ 2 * (b ^ 2 - 2 * b), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 2 * (b ^ 2 - 2 * b)))).mpr ⟨2 * m ^ 2 * (b ^ 2 - 2 * b), by parley_side⟩; parley_side)
      -- 2.4. mun:not-both n := a²·(b² − 2b), from 2.3
      have s2_4 : ¬ Odd (a ^ 2 * (b ^ 2 - 2 * b)) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s2_3) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s2_3)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s2_3) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s2_3) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s2_3); parley_side)
      all_goals parley_side
    · skip
      all_goals parley_side
  -- 3. mun:even-or-odd n := b
  have s3 : Even b ∨ Odd b := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)); parley_side)
  -- 4. cases, from 3
  have s4 : Odd b := by
    rcases s3 with hC3 | hC4
    · skip
      -- 4.1. obtain m: def:even n := b, from C3
      obtain ⟨m, s4_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side)
      -- 4.2. algebra, from 4.1
      have s4_2 : a ^ 2 * (b ^ 2 - 2 * b) = 2 * (a ^ 2 * (2 * m ^ 2 - 2 * m)) := by linear_combination (norm := parley_norm) (a ^ 2 * b + 2 * a ^ 2 * m - 2 * a ^ 2) * s4_1
      -- 4.3. def:even n := a²·(b² − 2b), from 4.2
      have s4_3 : Even (a ^ 2 * (b ^ 2 - 2 * b)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 2 * (b ^ 2 - 2 * b)))).mpr ⟨a ^ 2 * (2 * m ^ 2 - 2 * m), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 2 * (b ^ 2 - 2 * b)))).mpr ⟨a ^ 2 * (2 * m ^ 2 - 2 * m), by parley_side⟩; parley_side)
      -- 4.4. mun:not-both n := a²·(b² − 2b), from 4.3
      have s4_4 : ¬ Odd (a ^ 2 * (b ^ 2 - 2 * b)) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s4_3) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s4_3)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s4_3) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s4_3) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s4_3); parley_side)
      all_goals parley_side
    · skip
      all_goals parley_side
  -- 5. join 2, 4
  have s5 : Odd a ∧ Odd b := by parley_side
  all_goals exact s5

end Parley.Proofs.Hammack.OddProductOddFactors.OddProductOddFactors

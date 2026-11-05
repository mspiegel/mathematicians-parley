module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/both-even-from-product-and-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BothEvenFromProductAndSum.BothEvenFromProductAndSum

set_option maxHeartbeats 400000 in
theorem both_even_from_product_and_sum (a : ℤ) (b : ℤ) (hH3 : Even (a * b)) (hH4 : Even (a + b)) :
    (Even a ∧ Even b) := by
  -- 1. mun:even-product-factor, from H3
  have s1 : Even a ∨ Even b := by first | exact ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp (by parley_side); parley_side)
  -- 2. obtain m: def:even n := a + b, from H4
  obtain ⟨m, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a + b))).mp (by parley_side)
  -- 3. cases, from 1
  have s3 : Even a ∧ Even b := by
    rcases s1 with hC1 | hC2
    · skip
      -- 3.1. obtain j: def:even, from C1
      obtain ⟨j, s3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp (by parley_side)
      -- 3.2. algebra, from 2, 3.1
      have s3_2 : b = 2 * (m - j) := by linear_combination (norm := parley_norm) s2 + (-1) * s3_1
      -- 3.3. def:even n := b, from 3.2
      have s3_3 : Even b := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mpr ⟨m - j, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mpr ⟨m - j, by parley_side⟩; parley_side)
      -- 3.4. join C1, 3.3
      have s3_4 : Even a ∧ Even b := by parley_side
      all_goals parley_side
    · skip
      -- 3.5. obtain j: def:even, from C2
      obtain ⟨j, s3_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side)
      -- 3.6. algebra, from 2, 3.5
      have s3_6 : a = 2 * (m - j) := by linear_combination (norm := parley_norm) s2 + (-1) * s3_5
      -- 3.7. def:even n := a, from 3.6
      have s3_7 : Even a := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mpr ⟨m - j, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mpr ⟨m - j, by parley_side⟩; parley_side)
      -- 3.8. join C2, 3.7
      have s3_8 : Even a ∧ Even b := by parley_side
      all_goals parley_side
  all_goals exact s3

end Parley.Proofs.Hammack.BothEvenFromProductAndSum.BothEvenFromProductAndSum

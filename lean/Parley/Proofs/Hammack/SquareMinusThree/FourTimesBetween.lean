module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/square-minus-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween

theorem four_times_between (j : ℤ) (r : ℤ) (hH3 : r > 0) (hH4 : r < 4) :
    4 * j ≠ r := by
  -- 1. mun:nonneg-or-neg x := j − 1
  have s1 : j - 1 ≥ 0 ∨ j - 1 < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := j - 1)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := j - 1))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := j - 1)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := j - 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := j - 1)); parley_side)
  -- 2. cases, from 1
  have s2 : 4 * j ≠ r := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. inequalities
      have s2_1 : 4 * j ≥ 4 := by parley_order
      -- 2.2. transitivity, from H4, 2.1
      have s2_2 : r < 4 * j := by parley_order
      -- 2.3. inequalities
      have s2_3 : 4 * j ≠ r := by parley_side
      all_goals parley_side
    · skip
      -- 2.4. inequalities, from C2
      have s2_4 : j < 1 := by parley_order
      -- 2.5. mun:integer-step m := j, n := 1, from 2.4
      have s2_5 : j + 1 ≤ 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := j) (n := (1 : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := j) (n := (1 : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := j) (n := (1 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := j) (n := (1 : ℤ)) (by parley_side)); parley_side)
      -- 2.6. inequalities
      have s2_6 : 4 * j ≤ 0 := by parley_order
      -- 2.7. transitivity, from 2.6, H3
      have s2_7 : 4 * j < r := by parley_order
      -- 2.8. inequalities
      have s2_8 : 4 * j ≠ r := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween

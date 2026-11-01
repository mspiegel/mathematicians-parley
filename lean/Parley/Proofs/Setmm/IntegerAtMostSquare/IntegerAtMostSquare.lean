module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/integer-at-most-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.IntegerAtMostSquare.IntegerAtMostSquare

theorem integer_at_most_square (n : ℤ) :
    n ≤ n ^ 2 := by
  -- 1. axi:trichotomy x := n
  have s1 : (n < 0 ∨ n = 0) ∨ 0 < n := by first | exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := n)) | exact ((Parley.Items.Stdlib.Numbers.axi_trichotomy (x := n))).symm | simpa using (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := n))
  -- 2. mun:square-nonneg x := n
  have s2 : n ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := n))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := n)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := n))
  -- 3. algebra
  have s3 : n ^ 2 = n * n := by parley_ring
  -- 4. cases, from 1
  have s4 : n ≤ n ^ 2 := by
    rcases s1 with (hC1 | hC2) | hC3
    · skip
      -- 4.1. inequalities, from C1, 2
      have s4_1 : n < n ^ 2 := by parley_side
      -- 4.2. inequalities
      have s4_2 : n ≤ n ^ 2 := by parley_side
      all_goals parley_side
    · skip
      -- 4.3. algebra, from C2
      have s4_3 : n * n = 0 := by linear_combination (norm := parley_norm) (n) * hC2
      -- 4.4. transitivity, from C2, 4.3, 3
      have s4_4 : n = n ^ 2 := by parley_side
      -- 4.5. inequalities
      have s4_5 : n ≤ n ^ 2 := by parley_side
      all_goals parley_side
    · skip
      -- 4.6. mun:integer-step m := 0, from C3
      have s4_6 : 1 ≤ n := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (0 : ℤ)) (n := n) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (0 : ℤ)) (n := n) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (0 : ℤ)) (n := n) (by parley_side))
      -- 4.7. mun:multiply-le x := 1, y := n, c := n, from C3, 4.6
      have s4_7 : n * 1 ≤ n * n := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := n) (c := n) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := n) (c := n) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := n) (c := n) (by parley_side) (by parley_side))
      -- 4.8. inequalities
      have s4_8 : n ≤ n ^ 2 := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.IntegerAtMostSquare.IntegerAtMostSquare

module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/bernoulli-inequality.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct

theorem nonnegative_product (x : ℝ) (y : ℝ) (hH3 : 0 ≤ x) (hH4 : 0 ≤ y) :
    0 ≤ x * y := by
  -- 1. axi:trichotomy
  have s1 : (x < 0 ∨ x = 0) ∨ 0 < x := by first | exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := x)) | exact ((Parley.Items.Stdlib.Numbers.axi_trichotomy (x := x))).symm | simpa using (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := x))
  -- 2. cases, from 1
  have s2 : 0 ≤ x * y := by
    rcases s1 with (hC1 | hC2) | hC3
    · skip
      -- 2.1. inequalities, from C1
      have s2_1 : ¬ 0 ≤ x := by parley_side
      all_goals parley_side
    · skip
      -- 2.2. algebra, from C2
      have s2_2 : x * y = 0 := by linear_combination (norm := parley_norm) (y) * hC2
      -- 2.3. inequalities
      have s2_3 : 0 ≤ x * y := by parley_side
      all_goals parley_side
    · skip
      -- 2.4. mun:multiply-le x := 0, c := x, from C3, H4
      have s2_4 : x * 0 ≤ x * y := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (0 : ℝ)) (y := y) (c := x) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (0 : ℝ)) (y := y) (c := x) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (0 : ℝ)) (y := y) (c := x) (by parley_side) (by parley_side))
      -- 2.5. inequalities, from 2.4
      have s2_5 : 0 ≤ x * y := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct

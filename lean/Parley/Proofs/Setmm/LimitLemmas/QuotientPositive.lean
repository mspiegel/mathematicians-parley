module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/limit-lemmas.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitLemmas.QuotientPositive

theorem quotient_positive (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) :
    x / y > 0 := by
  -- 1. mun:quotient-nonneg, from H4
  have r35_1 : x ≥ 0 := by parley_side
  have s1 : x / y ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x) (y := y) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x) (y := y) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x) (y := y) (by parley_side) (by parley_side))
  -- 2. contradiction
  have s2 : x / y ≠ 0 := by
    by_contra hc_hS
    have hS : x / y = 0 := by parley_suppose hc_hS
    -- 2.1. algebra, from S
    have r43_1 : y ≠ 0 := by parley_side
    have s2_1 : x = 0 := by linear_combination (norm := parley_field) (y) * hS
    -- 2.2. inequalities
    have s2_2 : x ≠ 0 := by parley_side
    all_goals parley_side
  -- 3. inequalities, from 1, 2
  have r52_1 : y ≠ 0 := by parley_side
  have s3 : x / y > 0 := by parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.LimitLemmas.QuotientPositive

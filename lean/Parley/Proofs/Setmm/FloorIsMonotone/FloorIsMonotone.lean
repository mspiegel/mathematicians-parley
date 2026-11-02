module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-is-monotone.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorIsMonotone.FloorIsMonotone

theorem floor_is_monotone (A : ℝ) (B : ℝ) (hH3 : A ≤ B) :
    ⌊A⌋ ≤ ⌊B⌋ := by
  -- 1. mun:floor-integer x := A
  -- 2. mun:floor-integer x := B
  -- 3. mun:floor-below x := A
  have s3 : (⌊A⌋ : ℝ) ≤ A := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_below (x := A))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)); parley_side)
  -- 4. mun:floor-above x := B
  have s4 : B < (⌊B⌋ : ℝ) + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_above (x := B))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := B)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_above (x := B)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := B)); parley_side)
  -- 5. contradiction
  have s5 : ⌊A⌋ ≤ ⌊B⌋ := by
    by_contra hc_hS
    have hS : ¬ ⌊A⌋ ≤ ⌊B⌋ := by parley_suppose hc_hS
    -- 5.1. inequalities, from S
    have s5_1 : ⌊B⌋ < ⌊A⌋ := by parley_order
    -- 5.2. mun:integer-step m := ⌊B⌋, n := ⌊A⌋, from 1, 2, 5.1
    have s5_2 : ⌊B⌋ + 1 ≤ ⌊A⌋ := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊B⌋) (n := ⌊A⌋) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊B⌋) (n := ⌊A⌋) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊B⌋) (n := ⌊A⌋) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊B⌋) (n := ⌊A⌋) (by parley_side)); parley_side)
    -- 5.3. transitivity, from 5.2, 3, H3
    have s5_3 : (⌊B⌋ : ℝ) + 1 ≤ B := by parley_order
    -- 5.4. inequalities, from 5.3
    have s5_4 : ¬ B < (⌊B⌋ : ℝ) + 1 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.FloorIsMonotone.FloorIsMonotone

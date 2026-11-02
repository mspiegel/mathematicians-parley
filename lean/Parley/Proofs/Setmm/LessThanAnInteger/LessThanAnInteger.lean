module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/less-than-an-integer.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LessThanAnInteger.LessThanAnInteger

theorem less_than_an_integer (A : ℝ) (B : ℤ) :
    (A < (B : ℝ) ↔ ⌊A⌋ < B) := by
  -- 1. mun:floor-integer x := A
  -- 2. mun:floor-below x := A
  have s2 : (⌊A⌋ : ℝ) ≤ A := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_below (x := A))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)); parley_side)
  -- 3. mun:floor-above x := A
  have s3 : A < (⌊A⌋ : ℝ) + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_above (x := A))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A)); parley_side)
  -- 4. both directions
  have s4 : A < (B : ℝ) ↔ ⌊A⌋ < B := by
    constructor
    · skip
      intro hC1
      -- 4.1. transitivity, from 2, C1
      have s4_1 : ⌊A⌋ < B := by parley_side
      all_goals parley_side
    · skip
      intro hC2
      -- 4.2. mun:integer-step m := ⌊A⌋, n := B, from C2, 1
      have s4_2 : ⌊A⌋ + 1 ≤ B := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊A⌋) (n := B) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊A⌋) (n := B) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊A⌋) (n := B) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊A⌋) (n := B) (by parley_side)); parley_side)
      -- 4.3. transitivity, from 3, 4.2
      have s4_3 : A < (B : ℝ) := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.LessThanAnInteger.LessThanAnInteger

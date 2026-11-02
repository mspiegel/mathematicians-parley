module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/floor-add-integer.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorAddInteger.FloorAddInteger

theorem floor_add_integer (A : ℝ) (N : ℤ) :
    ⌊A + (N : ℝ)⌋ = ⌊A⌋ + N := by
  -- 1. mun:floor-integer x := A
  -- 2. mun:floor-below x := A
  have s2 : (⌊A⌋ : ℝ) ≤ A := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_below (x := A))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A))
  -- 3. mun:floor-above x := A
  have s3 : A < (⌊A⌋ : ℝ) + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_above (x := A))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A))
  -- 4. inequalities
  have s4 : (⌊A⌋ : ℝ) + (N : ℝ) ≤ A + (N : ℝ) := by parley_side
  -- 5. inequalities
  have s5 : A + (N : ℝ) < (⌊A⌋ : ℝ) + (N : ℝ) + 1 := by parley_side
  -- 6. mun:floor-between x := A + N, k := ⌊A⌋ + N, from 4, 5
  have s6 : ⌊A + (N : ℝ)⌋ = ⌊A⌋ + N := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := A + (N : ℝ)) (k := ⌊A⌋ + N))).mpr (by parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.FloorAddInteger.FloorAddInteger

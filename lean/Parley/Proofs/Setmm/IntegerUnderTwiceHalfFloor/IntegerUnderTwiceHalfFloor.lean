module

public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/integer-under-twice-half-floor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.IntegerUnderTwiceHalfFloor.IntegerUnderTwiceHalfFloor

theorem integer_under_twice_half_floor (N : ℤ) :
    N ≤ 2 * ⌊((N : ℝ) + 1) / 2⌋ := by
  set k : ℤ := ⌊((N : ℝ) + 1) / 2⌋ with hD1
  have hD1_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := ((N : ℝ) + 1) / 2)) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_integer (x := ((N : ℝ) + 1) / 2))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := ((N : ℝ) + 1) / 2)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := ((N : ℝ) + 1) / 2)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := ((N : ℝ) + 1) / 2)); parley_side)
  -- 1. mun:floor-above x := (N + 1)/2, from D1
  have s1 : ((N : ℝ) + 1) / 2 < (k : ℝ) + 1 := by
    try simp only [hD1] at *
    try push_cast at *
    first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_above (x := ((N : ℝ) + 1) / 2))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := ((N : ℝ) + 1) / 2)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_above (x := ((N : ℝ) + 1) / 2)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := ((N : ℝ) + 1) / 2)); parley_side)
  -- 2. inequalities
  have s2 : N < 2 * k + 1 := by parley_order
  -- 3. mun:integer-step m := N, n := 2k + 1, from 2
  have s3 : N + 1 ≤ 2 * k + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := N) (n := 2 * k + 1) s2)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N) (n := 2 * k + 1) s2); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N) (n := 2 * k + 1) s2) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N) (n := 2 * k + 1) s2); parley_side)
  -- 4. inequalities, from D1, 3
  have s4 : N ≤ 2 * ⌊((N : ℝ) + 1) / 2⌋ := by parley_order
  all_goals exact s4

end Parley.Proofs.Setmm.IntegerUnderTwiceHalfFloor.IntegerUnderTwiceHalfFloor

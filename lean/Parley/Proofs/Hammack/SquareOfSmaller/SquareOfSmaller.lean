module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/square-of-smaller.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareOfSmaller.SquareOfSmaller

theorem square_of_smaller (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) (hH5 : x < y) :
    x ^ 2 < y ^ 2 := by
  -- 1. mun:less-scaled c := x, from H3, H5
  have s1 : x * x < x * y := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := x) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := x) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := x) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := x) (by parley_side))).mp (by parley_side); parley_side)
  -- 2. mun:less-scaled c := y, from H4, H5
  have s2 : y * x < y * y := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := y) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := y) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := y) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := y) (by parley_side))).mp (by parley_side); parley_side)
  -- 3. algebra
  have s3 : x ^ 2 = x * x := by parley_ring
  -- 4. algebra
  have s4 : x * y = y * x := by parley_ring
  -- 5. algebra
  have s5 : y * y = y ^ 2 := by parley_ring
  -- 6. transitivity, from 3, 1, 4, 2, 5
  have s6 : x ^ 2 < y ^ 2 := by parley_order
  all_goals exact s6

end Parley.Proofs.Hammack.SquareOfSmaller.SquareOfSmaller

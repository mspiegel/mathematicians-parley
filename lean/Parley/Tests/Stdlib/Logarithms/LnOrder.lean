module

public import LeanBridges
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnOrder

theorem ln_order (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) :
    (x < y ↔ Real.log x < Real.log y) := by
  -- 1. mun:logarithms-ln-order, from H3, H4
  have s1 : x < y ↔ Real.log x < Real.log y := by first | exact (Parley.Items.Stdlib.Logarithms.mun_ln_order (x := x) (y := y) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Logarithms.mun_ln_order (x := x) (y := y) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Logarithms.mun_ln_order (x := x) (y := y) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_order (x := x) (y := y) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_order (x := x) (y := y) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_order (x := x) (y := y) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Logarithms.LnOrder

module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ReciprocalOrderStrict

theorem reciprocal_order_strict (x : ℝ) (hH2 : x > 0) (y : ℝ) (hH4 : y > 0) :
    (x < y ↔ 1 / y < 1 / x) := by
  -- 1. mun:numbers-reciprocal-order-strict, from H2, H4
  have s1 : x < y ↔ 1 / y < 1 / x := by first | exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := x) (by parley_side) (y := y) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := x) (by parley_side) (y := y) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := x) (by parley_side) (y := y) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := x) (by parley_side) (y := y) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := x) (by parley_side) (y := y) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := x) (by parley_side) (y := y) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.ReciprocalOrderStrict

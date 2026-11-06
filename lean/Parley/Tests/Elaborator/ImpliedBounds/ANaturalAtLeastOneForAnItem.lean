module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/implied-bounds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ImpliedBounds.ANaturalAtLeastOneForAnItem

theorem a_natural_at_least_one_for_an_item (n : ℤ) (hH1 : 0 < n) (c : ℝ) (hH3 : c > 0) :
    c * 1 ≤ c * (n : ℝ) := by
  -- 1. mun:multiply-le x := 1, y := n, from H1, H3
  have s1 : c * 1 ≤ c * (n : ℝ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := c) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := c) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := c) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := c) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ImpliedBounds.ANaturalAtLeastOneForAnItem

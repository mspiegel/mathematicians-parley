module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/implied-bounds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ImpliedBounds.ANaturalAtLeastOneForAnItem

theorem a_natural_at_least_one_for_an_item (n : ℤ) (hH1 : 0 < n) (c : ℝ) (hH3 : c > 0) :
    c * 1 ≤ c * (n : ℝ) := by
  -- 1. mun:multiply-le x := 1, y := n, from H1, H3
  exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := c) (by exact_mod_cast ge_iff_le.mp hH1) hH3)

end Parley.Tests.Elaborator.ImpliedBounds.ANaturalAtLeastOneForAnItem

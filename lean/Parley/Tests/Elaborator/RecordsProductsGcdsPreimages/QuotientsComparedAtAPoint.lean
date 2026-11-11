module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.QuotientsComparedAtAPoint

theorem quotients_compared_at_a_point (x : ℝ) (hH2 : 0 ≤ x) (hH3 : x ≤ 1) :
    x / 4 ≤ 1 / 2 := by
  -- 1. mun:quotients-compared y := 4, z := 1, w := 2, from H2, H3
  have r68_1 : (0 : ℤ) < 2 := by parley_arith
  have r68_2 : (2 : ℤ) ≤ 4 := by parley_arith
  exact (Parley.Items.Stdlib.Numbers.mun_quotients_compared (x := x) (y := (4 : ℝ)) (z := (1 : ℝ)) (w := (2 : ℝ)) hH2 hH3 (by parley_side) (by parley_side))

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.QuotientsComparedAtAPoint

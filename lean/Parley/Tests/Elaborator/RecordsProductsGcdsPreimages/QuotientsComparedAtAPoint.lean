module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.QuotientsComparedAtAPoint

theorem quotients_compared_at_a_point (x : ℝ) (hH2 : 0 ≤ x) (hH3 : x ≤ 1) :
    x / 4 ≤ 1 / 2 := by
  -- 1. mun:quotients-compared y := 4, z := 1, w := 2, from H2, H3
  have r68_1 : (0 : ℤ) < 2 := by norm_num
  have r68_2 : (2 : ℤ) ≤ 4 := by norm_num
  exact (Parley.Items.Stdlib.Numbers.mun_quotients_compared (x := x) (y := (4 : ℝ)) (z := (1 : ℝ)) (w := (2 : ℝ)) hH2 hH3 (by norm_num) (by norm_num))

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.QuotientsComparedAtAPoint

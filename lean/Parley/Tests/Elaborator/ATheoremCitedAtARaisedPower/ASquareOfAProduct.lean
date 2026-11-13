module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-theorem-cited-at-a-raised-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.ASquareOfAProduct

theorem a_square_of_a_product (a : ℝ) (b : ℝ) :
    (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
  -- 1. mun:power-of-product n := 2
  exact (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := a) (b := b) (n := (2 : ℤ)) (by norm_num))

end Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.ASquareOfAProduct

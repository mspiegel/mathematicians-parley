module

public import ArithTactics
public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.APowerOfAPositiveBase

theorem a_power_of_a_positive_base (n : ℤ) (hH1 : 0 < n) :
    (2 ^ n.toNat : ℤ) > 0 := by
  -- 1. mun:power-positive a := 2, m := n
  have r58_1 : (2 : ℤ) > 0 := by parley_arith
  have hI : (0 : ℤ) < 2 ^ n.toNat := by parley_instance_cast ((Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side)))
  exact hI

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.APowerOfAPositiveBase

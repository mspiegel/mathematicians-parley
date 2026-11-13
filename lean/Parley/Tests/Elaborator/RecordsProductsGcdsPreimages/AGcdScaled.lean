module

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
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdScaled

theorem a_gcd_scaled (a : ℤ) (b : ℤ) :
    (Int.gcd (3 * a) (3 * b) : ℤ) = 3 * (Int.gcd a b : ℤ) := by
  -- 1. mun:gcd-scaled c := 3
  exact (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (3 : ℤ)) (by norm_num) (a := a) (b := b))

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdScaled

module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdScaled

theorem a_gcd_scaled (a : ℤ) (b : ℤ) :
    (Int.gcd (3 * a) (3 * b) : ℤ) = 3 * (Int.gcd a b : ℤ) := by
  -- 1. mun:gcd-scaled c := 3
  exact (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (3 : ℤ)) (by parley_side) (a := a) (b := b))

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdScaled

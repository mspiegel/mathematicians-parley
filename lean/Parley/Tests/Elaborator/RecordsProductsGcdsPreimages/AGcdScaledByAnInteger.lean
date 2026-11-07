module

public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdScaledByAnInteger

theorem a_gcd_scaled_by_an_integer (a : ℤ) (b : ℤ) (c : ℤ) :
    (Int.gcd (c * a) (c * b) : ℤ) = abs (c * (Int.gcd a b : ℤ)) := by
  -- 1. mun:gcd-scaled-integer
  have s1 : (Int.gcd (c * a) (c * b) : ℤ) = abs (c * (Int.gcd a b : ℤ)) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled_integer (c := c) (a := a) (b := b))
  all_goals exact s1

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdScaledByAnInteger

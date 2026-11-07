module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdNotOfTwoZeros

theorem a_gcd_not_of_two_zeros (a : ℤ) (b : ℤ) (hH3 : ¬ (a = 0 ∧ b = 0)) :
    0 < (Int.gcd a b : ℤ) := by
  -- 1. mun:gcd-natural, from H3
  have s1 : 0 < (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := b) hH3)
  all_goals exact s1

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdNotOfTwoZeros

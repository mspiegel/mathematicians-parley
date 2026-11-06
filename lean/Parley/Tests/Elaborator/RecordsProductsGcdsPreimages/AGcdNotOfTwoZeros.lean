module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdNotOfTwoZeros

theorem a_gcd_not_of_two_zeros (a : ℤ) (b : ℤ) (hH3 : ¬ (a = 0 ∧ b = 0)) :
    0 < (Int.gcd a b : ℤ) := by
  -- 1. mun:gcd-natural, from H3
  have s1 : 0 < (Int.gcd a b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := b) hH3) | exact ((Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := b) hH3)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := b) hH3) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := b) hH3) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := b) hH3); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdNotOfTwoZeros

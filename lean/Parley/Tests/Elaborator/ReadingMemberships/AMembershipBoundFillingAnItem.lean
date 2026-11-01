module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundFillingAnItem

theorem a_membership_bound_filling_an_item (k : ℕ) (hH1 : 0 < k) :
    (k : ℤ) ^ 2 > 0 := by
  -- 1. mun:square-positive x := k, from H1
  have s1 : (k : ℤ) ^ 2 > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_positive (x := (k : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := (k : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_positive (x := (k : ℤ)) (by parley_side))
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundFillingAnItem

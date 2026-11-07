module

public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundFillingAnItem

theorem a_membership_bound_filling_an_item (k : ℤ) (hH1 : 0 < k) :
    k ^ 2 > 0 := by
  -- 1. mun:square-positive x := k, from H1
  have s1 : k ^ 2 > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_positive (x := k) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := k) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_positive (x := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := k) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundFillingAnItem

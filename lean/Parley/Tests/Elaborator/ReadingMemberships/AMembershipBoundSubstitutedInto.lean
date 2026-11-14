module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundSubstitutedInto

theorem a_membership_bound_substituted_into (k : ℤ) (hH1 : 0 < k) (m : ℤ) (hH3 : k = m) :
    m > 0 := by
  -- 1. substitute k = m (H3) into H1
  exact Eq.subst (motive := (fun t : ℤ => t > 0)) hH3 hH1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundSubstitutedInto

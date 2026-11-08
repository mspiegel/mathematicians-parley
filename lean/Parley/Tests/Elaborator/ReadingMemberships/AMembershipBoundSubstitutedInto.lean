module

public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundSubstitutedInto

theorem a_membership_bound_substituted_into (k : ℤ) (hH1 : 0 < k) (m : ℤ) (hH3 : k = m) :
    m > 0 := by
  -- 1. substitute k = m (H3) into H1
  parley_subst_at hH3 hH1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundSubstitutedInto

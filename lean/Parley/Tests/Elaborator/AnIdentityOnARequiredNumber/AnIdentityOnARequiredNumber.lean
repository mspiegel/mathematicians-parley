module

public import AlgebraTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/an-identity-on-a-required-number.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIdentityOnARequiredNumber.AnIdentityOnARequiredNumber

theorem an_identity_on_a_required_number (b : ℤ → ℤ) (hH1 : Set.MapsTo b (Set.univ : Set ℤ) {n : ℤ | 0 < n}) (A : ℤ) :
    b A * b A = 1 * (b A * b A) := by
  -- 1. membership, from H1
  have s1 : 0 < b A := by parley_set_side
  -- 2. algebra
  have s2 : b A * b A = 1 * (b A * b A) := by parley_ring
  all_goals exact s2

end Parley.Tests.Elaborator.AnIdentityOnARequiredNumber.AnIdentityOnARequiredNumber

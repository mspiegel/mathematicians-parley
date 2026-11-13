module

public import AlgebraTactics
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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-requires-line-at-a-member-by-the-table.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARequiresLineAtAMemberByTheTable.ARequiresLineAtAMemberByTheTable

theorem a_requires_line_at_a_member_by_the_table (m : ℤ) (hH1 : 0 < m) (F : ℤ → ℤ) (hD1 : F 0 = (1 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1)) :
    F m + F (m + 1) = F (m + 1) + F m := by
  -- 1. algebra
  parley_ring

end Parley.Tests.Elaborator.ARequiresLineAtAMemberByTheTable.ARequiresLineAtAMemberByTheTable

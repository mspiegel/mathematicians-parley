module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInARequiresLineCitingAnItem

theorem a_membership_bound_in_a_requires_line_citing_an_item (x : ℝ) (hH2 : x ≠ 0) (k : ℤ) (hH3 : 0 < k) :
    (x * (k : ℝ)) ^ 2 > 0 := by
  -- 1. mun:square-positive x := x·k
  have r173_1 : x * (k : ℝ) ≠ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := (k : ℝ)) hH2 (by exact_mod_cast hH3.ne'))
  exact (Parley.Items.Stdlib.Numbers.mun_square_positive (x := x * (k : ℝ)) r173_1)

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInARequiresLineCitingAnItem

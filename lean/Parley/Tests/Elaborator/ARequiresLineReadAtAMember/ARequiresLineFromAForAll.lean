module

public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-requires-line-read-at-a-member.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARequiresLineReadAtAMember.ARequiresLineFromAForAll

theorem a_requires_line_from_a_for_all (n : ℤ) (hH1 : 0 < n) (hH2 : ∀ m : ℤ, 0 < m → (2 ^ m.toNat : ℤ) > 0) :
    (1 / 2 ^ n.toNat : ℚ) > 0 := by
  -- 1. mun:reciprocal-positive x := 2^n
  have r19_1 : (2 ^ n.toNat : ℤ) > 0 := by parley_side
  exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by exact_mod_cast gt_iff_lt.mp r19_1))

end Parley.Tests.Elaborator.ARequiresLineReadAtAMember.ARequiresLineFromAForAll

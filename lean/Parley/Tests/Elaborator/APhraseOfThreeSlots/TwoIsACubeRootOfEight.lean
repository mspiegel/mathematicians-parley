module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Tests.Elaborator.APhraseOfThreeSlots

/-! Written from tests/elaborator/a-phrase-of-three-slots.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseOfThreeSlots.TwoIsACubeRootOfEight

theorem two_is_a_cube_root_of_eight :
    ((0 : ℤ) < 3 ∧ (2 ^ 3 : ℤ) = 8) := by
  -- 1. arithmetic
  have s1 : (2 ^ 3 : ℤ) = 8 := by norm_num
  -- 2. D1 z := 2, n := 3, w := 8, from 1
  exact ⟨by norm_num, by norm_num⟩

end Parley.Tests.Elaborator.APhraseOfThreeSlots.TwoIsACubeRootOfEight

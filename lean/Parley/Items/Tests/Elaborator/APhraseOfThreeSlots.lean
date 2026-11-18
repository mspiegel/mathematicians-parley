module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/a-phrase-of-three-slots.proof by parley build lean. -/

public section

namespace Parley.Items.Tests.Elaborator.APhraseOfThreeSlots

theorem def_nth_root {K : Type*} [Field K] [CharZero K] (n : ℤ) (w : K) (z : K) :
    0 < n ∧ z ^ n = w ↔ 0 < n ∧ z ^ n = w :=
  Iff.rfl

end Parley.Items.Tests.Elaborator.APhraseOfThreeSlots

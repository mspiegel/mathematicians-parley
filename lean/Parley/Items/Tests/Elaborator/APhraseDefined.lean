module

public import Tactics
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/a-phrase-defined.proof by parley build lean. -/

public section

namespace Parley.Items.Tests.Elaborator.APhraseDefined

theorem def_triangular_number {K : Type*} [Field K] [CharZero K] (n : K) :
    (∃ m : ℤ, 0 < m ∧ (m : K) = n) ∧ (∃ k : ℤ, 0 < k ∧ n = (k : K) * ((k : K) + 1) / 2) ↔ (∃ m : ℤ, 0 < m ∧ (m : K) = n) ∧ (∃ k : ℤ, 0 < k ∧ n = (k : K) * ((k : K) + 1) / 2) :=
  Iff.rfl

end Parley.Items.Tests.Elaborator.APhraseDefined

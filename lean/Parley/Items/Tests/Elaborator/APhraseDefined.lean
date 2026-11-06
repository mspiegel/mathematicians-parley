module

public import Tactics
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/a-phrase-defined.proof by parley build lean. -/

public section

namespace Parley.Items.Tests.Elaborator.APhraseDefined

theorem def_triangular_number {K : Type*} [Field K] [CharZero K] (n : K) :
    (∃ m : ℤ, 0 < m ∧ (m : K) = n) ∧ (∃ k : ℤ, 0 < k ∧ n = (k : K) * ((k : K) + 1) / 2) ↔ (∃ m : ℤ, 0 < m ∧ (m : K) = n) ∧ (∃ k : ℤ, 0 < k ∧ n = (k : K) * ((k : K) + 1) / 2) :=
  Iff.rfl

end Parley.Items.Tests.Elaborator.APhraseDefined

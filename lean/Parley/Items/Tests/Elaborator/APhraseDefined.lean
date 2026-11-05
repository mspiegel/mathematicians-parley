module

public import Tactics

/-! Written from tests/elaborator/a-phrase-defined.proof by parley build lean. -/

public section

namespace Parley.Items.Tests.Elaborator.APhraseDefined

theorem def_triangular_number {K : Type*} [Field K] [CharZero K] (n : K) :
    (∃ m : ℕ, 0 < m ∧ (m : K) = n) ∧ (∃ k : ℕ, 0 < k ∧ n = (k : K) * ((k : K) + 1) / 2) ↔ (∃ m : ℕ, 0 < m ∧ (m : K) = n) ∧ (∃ k : ℕ, 0 < k ∧ n = (k : K) * ((k : K) + 1) / 2) :=
  Iff.rfl

end Parley.Items.Tests.Elaborator.APhraseDefined

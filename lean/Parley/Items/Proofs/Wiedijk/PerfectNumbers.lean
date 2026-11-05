module

public import Tactics

/-! Written from proofs/wiedijk/perfect-numbers.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.PerfectNumbers

theorem def_power_times_odd (j : ℂ) :
    (∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ j = 2 ^ k * (m : ℂ))) ↔ (∃ k : ℕ, ∃ m : ℕ, 0 < m ∧ (Odd (m : ℤ) ∧ j = 2 ^ k * (m : ℂ))) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.PerfectNumbers

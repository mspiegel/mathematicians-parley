module

public import Tactics

/-! Written from proofs/wiedijk/perfect-numbers.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.PerfectNumbers

theorem def_power_times_odd (j : ℂ) :
    (∃ k : ℤ, 0 ≤ k ∧ (∃ m : ℤ, 0 < m ∧ (Odd m ∧ j = 2 ^ k.toNat * (m : ℂ)))) ↔ (∃ k : ℤ, 0 ≤ k ∧ (∃ m : ℤ, 0 < m ∧ (Odd m ∧ j = 2 ^ k.toNat * (m : ℂ)))) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.PerfectNumbers

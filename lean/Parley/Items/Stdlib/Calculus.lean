module

public import Calculus
public import Tactics

/-! Written from corpus/stdlib/calculus.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Calculus

theorem def_tends_to (x : ℤ → ℝ) (L : ℝ) :
    Filter.Tendsto (fun n : ℕ => (x (n : ℤ) : ℝ)) Filter.atTop (nhds L) ↔ (∀ ε : ℝ, 0 < ε → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (N : ℤ) ≤ (n : ℤ) → abs (x (n : ℤ) - L) < ε))) :=
  LeanBridges.Calculus.tends_to x L

end Parley.Items.Stdlib.Calculus

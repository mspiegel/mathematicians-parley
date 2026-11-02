module

public import Mathlib

/-!
# Calculus

What the library says of calculus, each item said in
Lean as the build writes it.
-/

public section

namespace LeanBridges.Calculus

/-- `def:stdlib/calculus/tends-to`. -/
theorem tends_to (x : ℤ → ℝ) (L : ℝ) :
    Filter.Tendsto (fun n : ℕ => (x (n : ℤ) : ℝ)) Filter.atTop (nhds L) ↔ (∀ ε : ℝ, 0 < ε → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (N : ℤ) ≤ (n : ℤ) → abs (x (n : ℤ) - L) < ε))) :=
  by rw [Metric.tendsto_atTop]; exact ⟨fun h ε hε => by obtain ⟨N, hN⟩ := h ε hε; exact ⟨N + 1, by omega, fun n _ hNn => by have := hN n (by omega); rwa [Real.dist_eq] at this⟩, fun h ε hε => by obtain ⟨N, _, hN⟩ := h ε hε; exact ⟨N + 1, fun n hn => by rw [Real.dist_eq]; exact hN n (by omega) (by omega)⟩⟩

end LeanBridges.Calculus

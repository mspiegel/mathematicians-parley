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

/-- `def:stdlib/calculus/limit-at`: the limit of f at c over its domain D,
c left out, in ε and δ. -/
theorem limit_at (f : ℝ → ℝ) (D : Set ℝ) (_hf : Set.MapsTo f D (Set.univ : Set ℝ))
    (_h1 : D ⊆ (Set.univ : Set ℝ)) (c : ℝ) (L : ℝ) :
    Filter.Tendsto f (nhdsWithin c (D \ {c})) (nhds L) ↔ (∀ ε : ℝ, 0 < ε → (∃ δ : ℝ, 0 < δ ∧ (∀ x ∈ D, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [Real.dist_eq, Set.mem_sdiff, Set.mem_singleton_iff, gt_iff_lt]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hxc => h ⟨hx, hxc.1⟩ hxc.2⟩
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hxc => h x hx.1 ⟨hx.2, hxc⟩⟩

/-- `def:stdlib/calculus/continuous-on`: continuity at each point of D, in
ε and δ, the points near it taken within D. -/
theorem continuous_on (f : ℝ → ℝ) (D : Set ℝ) (_hf : Set.MapsTo f D (Set.univ : Set ℝ))
    (_h1 : D ⊆ (Set.univ : Set ℝ)) :
    ContinuousOn f D ↔ (∀ c ∈ D, ∀ ε : ℝ, 0 < ε → (∃ δ : ℝ, 0 < δ ∧ (∀ x ∈ D, abs (x - c) < δ → abs (f x - f c) < ε))) := by
  rw [Metric.continuousOn_iff]
  simp only [Real.dist_eq, gt_iff_lt]

end LeanBridges.Calculus

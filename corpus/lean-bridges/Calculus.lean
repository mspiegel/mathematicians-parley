module

public import Lean.Parser.Command
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Calculus

What the library says of calculus, each item said in
Lean as the build writes it.
-/

public section

namespace LeanBridges.Calculus

/-- `def:stdlib/calculus/tends-to`. -/
theorem tends_to (x : ℤ → ℝ) (L : ℝ) :
    Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L) ↔ (∀ ε : ℝ, 0 < ε → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → N ≤ n → abs (x n - L) < ε))) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max N 1, by omega, fun n _ hNn => ?_⟩
    have := hN n (le_trans (le_max_left _ _) hNn)
    rwa [Real.dist_eq] at this
  · intro h ε hε
    obtain ⟨N, hN0, hN⟩ := h ε hε
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact hN n (by omega) hn⟩

/-- `def:stdlib/calculus/limit-at`: the limit of f at c over its domain D,
c left out, in ε and δ. -/
theorem limit_at (f : ℝ → ℝ) (D : Set ℝ) (_h1 : D ⊆ (Set.univ : Set ℝ)) (c : ℝ) (L : ℝ) :
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
theorem continuous_on (f : ℝ → ℝ) (D : Set ℝ) (_h1 : D ⊆ (Set.univ : Set ℝ)) :
    ContinuousOn f D ↔ (∀ c ∈ D, ∀ ε : ℝ, 0 < ε → (∃ δ : ℝ, 0 < δ ∧ (∀ x ∈ D, abs (x - c) < δ → abs (f x - f c) < ε))) := by
  rw [Metric.continuousOn_iff]
  simp only [Real.dist_eq, gt_iff_lt]

/-- `def:stdlib/calculus/series-sum`: the value of a series from 1 is the
limit of its partial sums, where they have one. -/
theorem series_sum (t : ℤ → ℝ) (L : ℝ)
    (h2 : Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ) : ℝ))
      Filter.atTop (nhds L)) :
    Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ)) = L :=
  h2.limUnder_eq

/-- `def:stdlib/calculus/series-sum-from-zero`, the same from 0. -/
theorem series_sum_from_zero (t : ℤ → ℝ) (L : ℝ)
    (h2 : Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (0 : ℤ) n, (t k : ℝ) : ℝ))
      Filter.atTop (nhds L)) :
    Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (0 : ℤ) n, (t k : ℝ)) = L :=
  h2.limUnder_eq

end LeanBridges.Calculus

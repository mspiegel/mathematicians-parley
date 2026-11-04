module

public import Calculus
public import Tactics

/-! Written from corpus/stdlib/calculus.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Calculus

theorem def_interval (x : ℝ) (a : ℝ) (b : ℝ) :
    x ∈ (Set.Icc a b : Set ℝ) ↔ (True ∧ a ≤ x) ∧ x ≤ b :=
  by simp [Set.mem_Icc]

theorem mun_interval_real (a : ℝ) (b : ℝ) :
    (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) :=
  Set.subset_univ _

theorem def_continuous_on (f : ℝ → ℝ) (D : Set ℝ) (hf : Set.MapsTo f D (Set.univ : Set ℝ)) (h1 : D ⊆ (Set.univ : Set ℝ)) :
    ContinuousOn f D ↔ (∀ c ∈ D, ∀ ε : ℝ, 0 < ε → (∃ δ : ℝ, 0 < δ ∧ (∀ x ∈ D, abs (x - c) < δ → abs (f x - f c) < ε))) :=
  LeanBridges.Calculus.continuous_on f D hf h1

theorem def_limit_at (f : ℝ → ℝ) (D : Set ℝ) (hf : Set.MapsTo f D (Set.univ : Set ℝ)) (h1 : D ⊆ (Set.univ : Set ℝ)) (c : ℝ) (L : ℝ) :
    Filter.Tendsto f (nhdsWithin c (D \ {c})) (nhds L) ↔ (∀ ε : ℝ, 0 < ε → (∃ δ : ℝ, 0 < δ ∧ (∀ x ∈ D, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε))) :=
  LeanBridges.Calculus.limit_at f D hf h1 c L

theorem def_tends_to (x : ℤ → ℝ) (L : ℝ) :
    Filter.Tendsto (fun n : ℕ => (x (n : ℤ) : ℝ)) Filter.atTop (nhds L) ↔ (∀ ε : ℝ, 0 < ε → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (N : ℤ) ≤ (n : ℤ) → abs (x (n : ℤ) - L) < ε))) :=
  LeanBridges.Calculus.tends_to x L

theorem def_series_sum (t : ℤ → ℝ) (L : ℝ) (h2 : Filter.Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (t k : ℝ) : ℝ)) Filter.atTop (nhds L)) :
    Filter.limUnder Filter.atTop (fun n : ℕ => ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (t k : ℝ)) = L :=
  LeanBridges.Calculus.series_sum t L h2

theorem def_series_sum_from_zero (t : ℤ → ℝ) (L : ℝ) (h2 : Filter.Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (t k : ℝ) : ℝ)) Filter.atTop (nhds L)) :
    Filter.limUnder Filter.atTop (fun n : ℕ => ∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (t k : ℝ)) = L :=
  LeanBridges.Calculus.series_sum_from_zero t L h2

end Parley.Items.Stdlib.Calculus

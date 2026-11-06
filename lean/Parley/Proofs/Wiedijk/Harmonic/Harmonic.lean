module

public import ArithTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Proofs.Wiedijk.Harmonic.HarmonicUnbounded

/-! Written from proofs/wiedijk/harmonic.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Harmonic.Harmonic

theorem harmonic :
    ¬ (∃ L : ℝ, Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / (k : ℝ) : ℝ) : ℝ)) Filter.atTop (nhds L)) := by
  -- 1. contradiction
  have s1 : ¬ (∃ L : ℝ, Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / (k : ℝ) : ℝ) : ℝ)) Filter.atTop (nhds L)) := by
    by_contra hc_hS
    have hS : ∃ L : ℝ, Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / (k : ℝ) : ℝ) : ℝ)) Filter.atTop (nhds L) := by parley_suppose hc_hS
    -- 1.1. obtain L from S
    obtain ⟨L, s1_1⟩ := hS
    -- 1.2. obtain B: thm:convergent-bounded, from 1.1
    obtain ⟨B, s1_2⟩ := (Parley.Items.Stdlib.Calculus.thm_convergent_bounded (x := (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / (k : ℝ) : ℝ))) (L := L) (by parley_side))
    -- 1.3. obtain N: thm:harmonic-unbounded M := B
    obtain ⟨N, s1_3a, s1_3b⟩ := (Parley.Proofs.Wiedijk.Harmonic.HarmonicUnbounded.harmonic_unbounded (M := B))
    -- 1.4. instantiate m := N in line 1.2
    have s1_4 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (1 / (k : ℝ) : ℝ)) ≤ B := by first | linarith [(s1_2 N (by parley_side))] | (have h := (s1_2 N (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1_2 N (by parley_side)) | (have h := (s1_2 N (by parley_side)); parley_side)
    -- 1.5. inequalities, from 1.4
    have s1_5 : ¬ (∑ k ∈ Finset.Icc (1 : ℤ) N, (1 / (k : ℝ) : ℝ)) > B := by parley_side
    all_goals parley_side
  all_goals exact s1

end Parley.Proofs.Wiedijk.Harmonic.Harmonic

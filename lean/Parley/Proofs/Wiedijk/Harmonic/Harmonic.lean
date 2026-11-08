module

public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Proofs.Wiedijk.Harmonic.HarmonicUnbounded

/-! Written from proofs/wiedijk/harmonic.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Harmonic.Harmonic

theorem harmonic :
    ¬ (∃ L : ℝ, Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / (k : ℝ) : ℝ) : ℝ)) Filter.atTop (nhds L)) := by
  -- 1. contradiction
  intro hS
  -- 1.1. obtain L from S
  obtain ⟨L, s1_1⟩ := hS
  -- 1.2. obtain B: thm:convergent-bounded, from 1.1
  obtain ⟨B, s1_2⟩ := (Parley.Items.Stdlib.Calculus.thm_convergent_bounded (x := (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / (k : ℝ) : ℝ))) (L := L) s1_1)
  -- 1.3. obtain N: thm:harmonic-unbounded M := B
  obtain ⟨N, s1_3a, s1_3b⟩ := (Parley.Proofs.Wiedijk.Harmonic.HarmonicUnbounded.harmonic_unbounded (M := B))
  -- 1.4. instantiate m := N in line 1.2
  have s1_4 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (1 / (k : ℝ) : ℝ)) ≤ B := by exact (s1_2 N (by parley_side))
  -- 1.5. inequalities, from 1.4
  have s1_5 : ¬ (∑ k ∈ Finset.Icc (1 : ℤ) N, (1 / (k : ℝ) : ℝ)) > B := by parley_side
  exact s1_5 s1_3b

end Parley.Proofs.Wiedijk.Harmonic.Harmonic

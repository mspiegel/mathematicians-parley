module

public import InstanceTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Functions
public import Parley.Proofs.Wiedijk.RealsUncountable.SequenceMissesReal

/-! Written from proofs/wiedijk/reals-uncountable.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.RealsUncountable.RealsUncountable

theorem reals_uncountable :
    ¬ (∃ g : ℤ → ℝ, Set.BijOn g {n : ℤ | 0 < n} (Set.univ : Set ℝ)) := by
  -- the theorem. contradiction
  intro hS
  -- 1. obtain f: mun:bijection-onto X := ℕ, Y := ℝ, from S
  obtain ⟨f, _, s1⟩ := (Parley.Items.Stdlib.Functions.mun_bijection_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℝ)) (by parley_whole_side))
  -- 2. def:onto, from 1
  have s2 : ∀ y : ℝ, ∃ n : ℤ, 0 < n ∧ y = f n := by
    have hI : ∀ y : ℝ, ∃ x : ℤ, 0 < x ∧ y = f x := by parley_instance_cast ((((Parley.Items.Stdlib.Functions.def_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mp s1).2)
    exact hI
  -- 3. obtain x: thm:sequence-misses-real
  obtain ⟨x, s3⟩ := (Parley.Proofs.Wiedijk.RealsUncountable.SequenceMissesReal.sequence_misses_real (f := f))
  -- 4. instantiate y := x in line 2
  have s4 : ∃ n : ℤ, 0 < n ∧ x = f n := by exact (s2 x)
  -- 5. obtain m from line 4
  obtain ⟨m, s5a, s5b⟩ := s4
  -- 6. instantiate n := m in line 3
  have s6 : x ≠ f m := by exact ((s3 m (by parley_set_side))).symm
  exact s6 s5b

end Parley.Proofs.Wiedijk.RealsUncountable.RealsUncountable

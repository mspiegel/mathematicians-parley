module

public import Divisibility
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/a-divides-fold-with-its-witness.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADividesFoldWithItsWitness.ADividesFoldWithItsWitness

theorem a_divides_fold_with_its_witness (m : ℝ) (hH2 : ∃ m₀ : ℤ, 0 < m₀ ∧ (m₀ : ℝ) = m) (hH3 : ∃ j : ℤ, ∃ k : ℤ, (j : ℝ) ^ 2 + (k : ℝ) ^ 2 = 3 * m ^ 2) :
    (∃ m₀ : ℤ, (m₀ : ℝ) = 3 * m ^ 2 ∧ (3 : ℤ) ∣ m₀) := by
  -- 1. obtain p, q from H3
  obtain ⟨p, q, s1⟩ := hH3
  -- 2. def:divides d := 3, n := p² + q², from H2, 1
  have s2 : (3 : ℤ) ∣ p ^ 2 + q ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p ^ 2 + q ^ 2))).mpr ⟨(by have named_witness : ∃ m₀ : ℤ, (m₀ : ℝ) = m ^ 2 := (by have whole1 : ∃ m₀ : ℤ, (m₀ : ℝ) = m := (by obtain ⟨m₀, _, hm⟩ := hH2; exact ⟨m₀, by exact_mod_cast hm⟩); exact ⟨((Classical.choose whole1 : ℤ) ^ 2), by (push_cast; simp only [Classical.choose_spec whole1]; all_goals ring)⟩); exact Classical.choose named_witness), by have named_witness : ∃ m₀ : ℤ, (m₀ : ℝ) = m ^ 2 := (by have whole1 : ∃ m₀ : ℤ, (m₀ : ℝ) = m := (by obtain ⟨m₀, _, hm⟩ := hH2; exact ⟨m₀, by exact_mod_cast hm⟩); exact ⟨((Classical.choose whole1 : ℤ) ^ 2), by (push_cast; simp only [Classical.choose_spec whole1]; all_goals ring)⟩); have := Classical.choose_spec named_witness; parley_side⟩
  -- 3. substitute p² + q² = 3m² (line 1) into line 2
  have whole1 : ∃ m₀ : ℤ, (m₀ : ℝ) = 3 * m ^ 2 := by obtain ⟨m₀, hm⟩ := (⟨p ^ 2 + q ^ 2, by exact_mod_cast s1⟩ : ∃ m₀ : ℤ, (m₀ : ℝ) = 3 * m ^ 2); exact ⟨m₀, by exact_mod_cast hm⟩
  (try rw [← (by exact_mod_cast Classical.choose_spec whole1 : ((Classical.choose whole1 : ℤ) : ℝ) = 3 * m ^ 2)] at s1; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)] at s1); norm_cast at s1)
  (try rw [← (by exact_mod_cast Classical.choose_spec whole1 : ((Classical.choose whole1 : ℤ) : ℝ) = 3 * m ^ 2)] at s2; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)] at s2); norm_cast at s2)
  refine ⟨(Classical.choose whole1 : ℤ), by (push_cast; simp only [Classical.choose_spec whole1]; all_goals ring), ?_⟩
  ((have h := Eq.subst (motive := (fun t : ℤ => (3 : ℤ) ∣ t)) s1 s2; push_cast at h ⊢; all_goals exact_mod_cast h))

end Parley.Tests.Elaborator.ADividesFoldWithItsWitness.ADividesFoldWithItsWitness

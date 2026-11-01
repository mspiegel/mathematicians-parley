module

public import Parley.Library

/-! Written from proofs/setmm/no-least-positive.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NoLeastPositive.NoLeastPositive

theorem no_least_positive :
    ¬ (∃ x : ℝ, 0 < x ∧ ¬ (∃ y : ℝ, 0 < y ∧ y < x)) := by
  -- 1. contradiction
  have s1 : ¬ (∃ x : ℝ, 0 < x ∧ ¬ (∃ y : ℝ, 0 < y ∧ y < x)) := by
    by_contra hc_S
    have S : ∃ x : ℝ, 0 < x ∧ ¬ (∃ y : ℝ, 0 < y ∧ y < x) := by parley_suppose hc_S
    -- 1.1. obtain x from S
    obtain ⟨x, s1_1a, s1_1b⟩ := S
    -- 1.2. inequalities
    have s1_2 : 0 < x / 2 := by parley_side
    -- 1.3. inequalities
    have s1_3 : x / 2 < x := by parley_side
    -- 1.4. exhibit, from 1.2, 1.3
    have s1_4 : ∃ y : ℝ, 0 < y ∧ y < x := ⟨x / 2, by parley_side⟩
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.NoLeastPositive.NoLeastPositive

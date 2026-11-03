module

public import Tactics

/-! Written from tests/elaborator/a-proof-block-ending-impossible.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AProofBlockEndingImpossible.NothingBelowOneIsTwo

theorem nothing_below_one_is_two :
    (∀ x : ℝ, x ≤ 1 ∧ x = 2 → x = 5) := by
  -- 1. proof
  have s1 : ∀ x : ℝ, x ≤ 1 ∧ x = 2 → x = 5 := by
    intro x
    intro hK2
    -- 1.1. restate K2
    have s1_1 : x ≤ 1 := by parley_side
    -- 1.2. substitute x = 2 (K2) into line 1.1
    have s1_2 : (2 : ℝ) ≤ 1 := by parley_subst_at hK2.2 s1_1
    exact absurd s1_2 (by norm_num)
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.AProofBlockEndingImpossible.NothingBelowOneIsTwo

module

public import Tactics

/-! Written from tests/elaborator/a-recursion-renamed.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARecursionRenamed.ARecursionRuleForAll

theorem a_recursion_rule_for_all (F : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1) :
    (∀ n : ℕ, F ((n : ℤ) + 1) = F (n : ℤ) + 1) := by
  -- 1. D1
  have s1 : ∀ n : ℕ, F ((n : ℤ) + 1) = F (n : ℤ) + 1 := by intro n; (have h := (hD1.2 (((n : ℤ) + 1) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith)
  all_goals exact s1

end Parley.Tests.Elaborator.ARecursionRenamed.ARecursionRuleForAll

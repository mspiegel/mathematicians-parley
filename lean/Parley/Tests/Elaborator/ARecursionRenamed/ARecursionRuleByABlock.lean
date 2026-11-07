module

public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring.RingNF

/-! Written from tests/elaborator/a-recursion-renamed.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARecursionRenamed.ARecursionRuleByABlock

theorem a_recursion_rule_by_a_block (F : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1) :
    (∀ n : ℤ, 0 ≤ n → F (n + 1) = F n + 1) := by
  -- 1. proof
  have s1 : ∀ n : ℤ, 0 ≤ n → F (n + 1) = F n + 1 := by
    intro n hK1
    -- 1.1. D1
    have s1_1 : F (n + 1) = F n + 1 := by have h := (hD1.2 ((n + 1) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
    all_goals exact s1_1
  all_goals exact s1

end Parley.Tests.Elaborator.ARecursionRenamed.ARecursionRuleByABlock

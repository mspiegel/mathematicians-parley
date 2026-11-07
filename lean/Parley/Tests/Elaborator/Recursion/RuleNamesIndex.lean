module

public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF

/-! Written from tests/elaborator/recursion.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Recursion.RuleNamesIndex

theorem rule_names_index (s : ℤ → ℤ) (hD1 : s 0 = (0 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → s (k + 1) = s k + k) :
    (s 0 = 0 ∧ s (1 + 1) = s 1 + 1) := by
  -- 1. D1
  have s1 : s 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
  -- 2. membership
  have s2 : (0 : ℤ) ≤ 1 := by parley_side
  -- 3. D1, from 2
  have s3 : s (1 + 1) = s 1 + 1 := by have h := (hD1.2 ((1 + 1 : ℤ) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 4. join 1, 3
  have s4 : s 0 = 0 ∧ s (1 + 1) = s 1 + 1 := by parley_side
  all_goals exact s4

end Parley.Tests.Elaborator.Recursion.RuleNamesIndex

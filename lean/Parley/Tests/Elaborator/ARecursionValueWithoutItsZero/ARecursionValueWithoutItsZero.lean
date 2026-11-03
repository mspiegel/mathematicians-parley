module

public import Tactics

/-! Written from tests/elaborator/a-recursion-value-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARecursionValueWithoutItsZero.ARecursionValueWithoutItsZero

theorem a_recursion_value_without_its_zero (F : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 2) :
    F (0 + 1) = 2 := by
  -- 1. D1
  have s1 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
  -- 2. D1
  have s2 : F 1 = F 0 + 2 := by have h := (hD1.2 ((1 : ℤ) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 3. algebra, from 1, 2
  have s3 : F (0 + 1) = 2 := by linear_combination (norm := parley_norm) s1 + s2
  all_goals exact s3

end Parley.Tests.Elaborator.ARecursionValueWithoutItsZero.ARecursionValueWithoutItsZero

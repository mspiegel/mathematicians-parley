module

public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF

/-! Written from tests/elaborator/recursion-shapes-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences

theorem two_sequences (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k)) :
    F 1 = 1 := by
  -- 1. D1
  have s1 : F (0 + 1) = G 0 := by have h := (hD1.2.2 ((0 + 1 : ℤ) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 2. D1
  have s2 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); linarith
  -- 3. calculation
  calc F 1 = F (0 + 1) := by norm_num
    _ = G 0 := s1
    _ = 1 := s2

end Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences

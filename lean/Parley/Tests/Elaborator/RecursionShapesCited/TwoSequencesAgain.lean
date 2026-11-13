module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences

/-! Written from tests/elaborator/recursion-shapes-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecursionShapesCited.TwoSequencesAgain

theorem two_sequences_again (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ (∀ n : ℤ, 0 ≤ n → F (n + 1) = G n ∧ G (n + 1) = F n + G n)) :
    F 1 = 1 := by
  -- 1. thm:two-sequences
  exact (Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences.two_sequences (F := F) (G := G) hD1)

end Parley.Tests.Elaborator.RecursionShapesCited.TwoSequencesAgain

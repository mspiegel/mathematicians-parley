module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/an-obtain-from-two-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnObtainFromTwoSentences.AnObtainFromTwoSentences

theorem an_obtain_from_two_sentences {α : Type*} [Nonempty α] (A : Set α) (u : α) (hH2 : u ∈ A) (hH3 : ∃ x ∈ A, x = u) :
    (∃ y ∈ A, y = u) := by
  -- 1. join H2, H3
  have s1a : u ∈ A := hH2
  have s1b : ∃ x ∈ A, x = u := hH3
  -- 2. obtain x from line 1
  obtain ⟨x, s2a, s2b⟩ := s1b
  -- 3. exhibit, from 2
  exact ⟨x, s2a, s2b⟩

end Parley.Tests.Elaborator.AnObtainFromTwoSentences.AnObtainFromTwoSentences

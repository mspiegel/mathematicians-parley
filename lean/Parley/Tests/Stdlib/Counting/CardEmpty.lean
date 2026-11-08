module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.CardEmpty

theorem card_empty {α : Type*} :
    ((∅ : Set α).ncard : ℤ) = 0 := by
  -- 1. mun:counting-card-empty
  exact Parley.Items.Stdlib.Counting.mun_card_empty

end Parley.Tests.Stdlib.Counting.CardEmpty

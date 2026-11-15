module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
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
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.PowerSetOfEmptyHasOneMember

theorem power_set_of_empty_has_one_member {α : Type*} :
    ((𝒫 (∅ : Set α)).ncard : ℤ) = 1 := by
  -- 1. mun:powerset-empty
  have s1 : 𝒫 (∅ : Set α) = ({∅} : Set (Set α)) := by exact Parley.Items.Stdlib.Sets.mun_powerset_empty
  -- 2. mun:card-singleton x := ∅
  have s2 : (({∅} : Set (Set α)).ncard : ℤ) = 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α)))
  -- 3. substitute 𝒫∅ = {∅} (line 1) into line 2
  exact Eq.subst (motive := (fun t : Set (Set α) => (t.ncard : ℤ) = 1)) s1.symm s2

end Parley.Tests.Notations.Sets.PowerSetOfEmptyHasOneMember

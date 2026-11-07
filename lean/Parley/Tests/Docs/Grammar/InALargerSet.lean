module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Sets

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.InALargerSet

theorem in_a_larger_set (x : ℤ) (hH1 : x ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) :
    x ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∪ ({(7 : ℤ)} : Set ℤ) := by
  set B : Set ℤ := ({(1 : ℤ), (2 : ℤ)} : Set ℤ) with h_B
  -- 1. mun:in-union-left, from H1
  have s1 : x ∈ B ∪ ({(7 : ℤ)} : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := ({(7 : ℤ)} : Set ℤ)) (u := x) hH1)
  all_goals parley_set_side

end Parley.Tests.Docs.Grammar.InALargerSet

module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.UnionFinite

theorem union_finite {α : Type*} (X : Set α) (Y : Set α) (hH3 : X.Finite) (hH4 : Y.Finite) :
    (X ∪ Y).Finite := by
  -- 1. mun:counting-union-finite, from H3, H4
  exact (Parley.Items.Stdlib.Counting.mun_union_finite (X := X) (Y := Y) hH3 hH4)

end Parley.Tests.Stdlib.Counting.UnionFinite

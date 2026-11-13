module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.InAUnion

theorem in_a_union :
    (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∪ ({(3 : ℤ)} : Set ℤ) := by
  -- 1. def:singleton x := 3, a := 3
  have s1 : (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ) := ((Parley.Items.Stdlib.Sets.def_singleton (a := (3 : ℤ)) (x := (3 : ℤ)))).mpr (by norm_num)
  -- 2. mun:or-right, from 1
  have s2 : (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∨ (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ) := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) s1)
  -- 3. def:union, from 2
  exact ((Parley.Items.Stdlib.Sets.def_union (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mpr s2

end Parley.Tests.Notations.Sets.InAUnion

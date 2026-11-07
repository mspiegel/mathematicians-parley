module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.InAUnion

theorem in_a_union :
    (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∪ ({(3 : ℤ)} : Set ℤ) := by
  -- 1. def:singleton x := 3, a := 3
  have s1 : (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_singleton (a := (3 : ℤ)) (x := (3 : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_singleton (a := (3 : ℤ)) (x := (3 : ℤ)))).mpr (by parley_set_side); parley_set_side)
  -- 2. mun:or-right, from 1
  have s2 : (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∨ (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) s1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) s1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) s1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) s1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) s1); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) s1); parley_set_side)
  -- 3. def:union, from 2
  have s3 : (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∪ ({(3 : ℤ)} : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_union (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s3

end Parley.Tests.Notations.Sets.InAUnion

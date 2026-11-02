module

public import LeanBridges
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.InAUnion

theorem in_a_union :
    (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∪ ({(3 : ℤ)} : Set ℤ) := by
  -- 1. def:singleton x := 3, a := 3
  have s1 : (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_singleton (a := (3 : ℤ)) (x := (3 : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_singleton (a := (3 : ℤ)) (x := (3 : ℤ)))).mpr (by parley_side); parley_side)
  -- 2. mun:or-right, from 1
  have s2 : (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∨ (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Q := (3 : ℤ) ∈ ({(3 : ℤ)} : Set ℤ)) (by parley_side)); parley_side)
  -- 3. def:union, from 2
  have s3 : (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∪ ({(3 : ℤ)} : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_union (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Tests.Notations.Sets.InAUnion

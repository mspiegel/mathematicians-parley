module

public import LeanBridges
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.APartOfASet

theorem a_part_of_a_set :
    ({(1 : ℤ)} : Set ℤ) ∈ 𝒫 ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by
  -- 1. arithmetic
  have s1 : (1 : ℤ) = 1 := by parley_arith
  -- 2. mun:or-left, from 1
  have s2 : (1 : ℤ) = 1 ∨ (1 : ℤ) = 2 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (1 : ℤ) = 1) (Q := (1 : ℤ) = 2) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := (1 : ℤ) = 1) (Q := (1 : ℤ) = 2) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (1 : ℤ) = 1) (Q := (1 : ℤ) = 2) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (1 : ℤ) = 1) (Q := (1 : ℤ) = 2) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (1 : ℤ) = 1) (Q := (1 : ℤ) = 2) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (1 : ℤ) = 1) (Q := (1 : ℤ) = 2) (by parley_side)); parley_side)
  -- 3. def:pair x := 1, u := 1, w := 2, from 2
  have s3 : (1 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_pair (x := (1 : ℤ)) (u := (1 : ℤ)) (w := (2 : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_pair (x := (1 : ℤ)) (u := (1 : ℤ)) (w := (2 : ℤ)))).mpr (by parley_side); parley_side)
  -- 4. mun:singleton-subset a := 1, X := {1, 2}, from 3
  have s4 : ({(1 : ℤ)} : Set ℤ) ⊆ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (a := (1 : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_singleton_subset (X := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (a := (1 : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (a := (1 : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (a := (1 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (a := (1 : ℤ)) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (a := (1 : ℤ)) (by parley_side)); parley_side)
  -- 5. def:powerset, from 4
  have s5 : ({(1 : ℤ)} : Set ℤ) ∈ 𝒫 ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (S := ({(1 : ℤ)} : Set ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (S := ({(1 : ℤ)} : Set ℤ)))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Tests.Notations.Sets.APartOfASet

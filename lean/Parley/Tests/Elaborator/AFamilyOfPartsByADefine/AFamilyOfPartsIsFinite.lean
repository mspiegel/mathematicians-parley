module

public import SetTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-family-of-parts-by-a-define.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AFamilyOfPartsIsFinite

theorem a_family_of_parts_is_finite (m : ℕ) (n : ℕ) :
    {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | (1 : ℤ) ∈ c}.Finite := by
  -- 1. mun:range-finite a := 1, b := m + n
  have s1 : (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ).Finite := by first | exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ))) | exact ((Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ))); parley_set_side)
  -- 2. proof
  have s2 : ∀ c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | (1 : ℤ) ∈ c}, c ⊆ (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) := by
    intro c hK1
    -- 2.1. def:set-builder u := c, from D1, K1
    have s2_1 : c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} := by first | exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)}) (u := c))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)}) (u := c))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)}) (u := c))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)}) (u := c))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)}) (u := c))).mp (by parley_set_side)).1; parley_set_side)
    -- 2.2. def:part-builder u := c, from 2.1
    have s2_2 : c ⊆ (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) := by first | exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = (m : ℤ))) (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (u := c))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = (m : ℤ))) (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (u := c))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = (m : ℤ))) (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (u := c))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = (m : ℤ))) (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (u := c))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = (m : ℤ))) (X := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (u := c))).mp (by parley_set_side)).1; parley_set_side)
    all_goals exact s2_2
  -- 3. mun:parts-finite A := {1, …, m + n}, K := K(m, n), from 1, 2
  have s3 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | (1 : ℤ) ∈ c}.Finite := by first | exact (Parley.Items.Stdlib.Counting.mun_parts_finite (A := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (K := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | (1 : ℤ) ∈ c}) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Counting.mun_parts_finite (A := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (K := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | (1 : ℤ) ∈ c}) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_parts_finite (A := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (K := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | (1 : ℤ) ∈ c}) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_parts_finite (A := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (K := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | (1 : ℤ) ∈ c}) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_parts_finite (A := (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (K := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | (1 : ℤ) ∈ c}) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  all_goals exact s3

end Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AFamilyOfPartsIsFinite
